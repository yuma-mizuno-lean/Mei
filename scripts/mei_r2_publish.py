#!/usr/bin/env python3
"""Conservative, fail-closed publisher for a trusted Lake publication plan.

R2 control state is never exposed by the public reader. Reserve bytes and PUTs
before uploading; never refund an ambiguous operation. A crash leaves a lock
requiring inspection, rather than permitting a second writer. No automatic GC.
"""
import argparse
import copy
from concurrent.futures import ThreadPoolExecutor
import datetime as dt
from email.utils import parsedate_to_datetime
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import urllib.parse
import uuid
import xml.etree.ElementTree as ET

LIMIT = 10_000_000_000
A_LIMIT = 20_000
STATE_KEY = '_control/budget.json'
STATE_ALLOWANCE = 65536
ART = re.compile(r'artifacts/yuma-mizuno-lean/Mei/[0-9a-f]{16}\.art\Z')
MAP = re.compile(r'revisions/yuma-mizuno-lean/Mei/tc/leanprover--lean4---[0-9A-Za-z][0-9A-Za-z._+-]*/[0-9a-f]{40}\.jsonl\Z')


class Stop(RuntimeError):
    """Abort publication without retry; prior remote writes may have succeeded."""


class S3:
    """Minimal signed transport for the dedicated mei-cache bucket.

    Construct with its HTTPS bucket endpoint and AccessKeyID:SecretAccessKey.
    Invalid endpoint or credential syntax raises Stop before any request.
    """
    def __init__(self, endpoint, credential):
        if not re.fullmatch(r'https://[0-9a-f]{32}\.r2\.cloudflarestorage\.com/mei-cache', endpoint):
            raise Stop('expected the exact R2 endpoint for mei-cache')
        if not re.fullmatch(r'[A-Za-z0-9]+:[A-Za-z0-9]+', credential):
            raise Stop('invalid credential format')
        self.endpoint, self.credential = endpoint, credential

    def request(self, method, key='', data=None, headers=None, query=None):
        """Return (HTTP status, response bytes, lowercase response headers).

        key is bucket-relative; query and headers are optional mappings. data
        is bytes or a Path to a frozen upload file, or None for no payload.
        HTTP errors are returned for the caller to inspect. Transport failures
        raise Stop with an uncertain remote outcome; requests are never retried.
        """
        url = self.endpoint + '/' + urllib.parse.quote(key, safe='/')
        if query:
            url += '?' + urllib.parse.urlencode(query)
        # Credentials go to curl stdin, never argv, logs, or a persistent file.
        config = 'user = ' + json.dumps(self.credential) + '\n'
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            args = ['curl', '--silent', '--show-error', '--proto', '=https',
                    '--aws-sigv4', 'aws:amz:auto:s3', '--config', '-',
                    '--connect-timeout', '15', '--max-time', '120',
                    '--request', method, '--output', str(root / 'body'),
                    '--dump-header', str(root / 'headers'), '--write-out', '%{http_code}']
            for name, value in (headers or {}).items():
                args += ['--header', f'{name}: {value}']
            if data is not None:
                if isinstance(data, Path):
                    payload = data
                else:
                    payload = root / 'payload'
                    payload.write_bytes(data)
                args += ['--upload-file', str(payload), '--header', 'x-amz-storage-class: STANDARD']
            args += ['--max-filesize', str(16 * 1024 * 1024), url]
            result = subprocess.run(args, input=config, text=True, capture_output=True)
            if result.returncode:
                raise Stop('R2 transport failed; outcome may be unknown; no retry')
            code = int(result.stdout)
            response_headers = {}
            for line in (root / 'headers').read_text().splitlines():
                if ':' in line:
                    name, value = line.split(':', 1)
                    response_headers[name.lower()] = value.strip()
            return code, (root / 'body').read_bytes(), response_headers


def initial_state():
    """Return a fresh in-memory budget, including control-object byte allowance.

    No remote state is created. day is unset, class_a is zero, and active is
    None until initialization or reservation supplies their operational values.
    """
    return dict(version=1, reserved_bytes=STATE_ALLOWANCE, day='', class_a=0, active=None)


def reserve(state, sizes, today, token):
    """Return a locked copy of state reserving payload bytes and publication PUTs.

    sizes is a sequence of nonnegative integer byte counts; today is the UTC
    ISO date and token identifies this attempt. active must be None. Bytes
    accumulate without refunds; class_a resets only on a later day. Invalid
    state, an existing lock, or exhausted limits raises Stop. This function
    performs no I/O: the caller must persist the result conditionally before
    uploading anything. The input state is not mutated.
    """
    state = copy.deepcopy(state)
    if (state.get('version') != 1 or type(state.get('reserved_bytes')) is not int
            or not STATE_ALLOWANCE <= state['reserved_bytes'] <= LIMIT
            or type(state.get('class_a')) is not int or not 0 <= state['class_a'] <= A_LIMIT
            or not isinstance(state.get('day'), str)):
        raise Stop('invalid budget state')
    if state.get('active') is not None:
        raise Stop('previous publisher is active or interrupted; inspection required')
    if not re.fullmatch(r'\d{4}-\d{2}-\d{2}', today) or state['day'] > today:
        raise Stop('invalid or reversed budget date')
    if any(type(size) is not int or size < 0 for size in sizes):
        raise Stop('invalid object size')
    # Count every candidate byte even when overwriting existing data. This upper
    # bound survives partial/ambiguous writes and never relies on delayed metrics.
    total = state['reserved_bytes'] + sum(sizes)
    if total > LIMIT:
        raise Stop('10 GB conservative storage budget exhausted')
    used = state['class_a'] if state['day'] == today else 0
    cost = len(sizes) + 2  # reservation PUT + uploads + completion PUT
    if used + cost > A_LIMIT:
        raise Stop('daily publication operation budget exhausted')
    state.update(reserved_bytes=total, day=today, class_a=used + cost, active=token)
    return state


def load_plan(directory, endpoint):
    """Validate a trusted frozen plan and return ordered (bucket key, Path) pairs.

    directory contains artifacts.curl, map-url and outputs.jsonl from the
    trusted planner. URLs must use endpoint; payloads must be regular files
    directly inside directory. The revision map is always the final pair.
    Reject unsafe directives, keys, paths and duplicates with Stop; malformed
    JSON or inaccessible files may raise ValueError or OSError. The caller
    must keep payloads immutable from validation through publication.
    """
    directory = directory.resolve()
    rows = (directory / 'artifacts.curl').read_text().splitlines()
    if len(rows) % 2 or len(rows) > 2 * A_LIMIT:
        raise Stop('invalid or oversized publication plan')
    objects = []
    def key_for(url):
        prefix = endpoint + '/'
        if not url.startswith(prefix):
            raise Stop('upload URL is outside the selected bucket')
        return url[len(prefix):]
    for i in range(0, len(rows), 2):
        if not rows[i].startswith('upload-file = ') or not rows[i + 1].startswith('url = '):
            raise Stop('unexpected curl directive')
        path = Path(json.loads(rows[i][14:]))
        key = key_for(json.loads(rows[i + 1][6:]))
        if not ART.fullmatch(key) or path.name != key.rsplit('/', 1)[1][:-4] + '.ltar':
            raise Stop('invalid artifact path')
        objects.append((key, path))
    key = key_for((directory / 'map-url').read_text().strip())
    if not MAP.fullmatch(key):
        raise Stop('invalid revision map path')
    objects.append((key, directory / 'outputs.jsonl'))
    if len({key for key, _ in objects}) != len(objects):
        raise Stop('duplicate upload key')
    for _, path in objects:
        if path.is_symlink() or path.resolve().parent != directory or not path.is_file():
            raise Stop('upload payload escapes the frozen plan')
    return objects


def initialize(client):
    """Create the remote budget once, returning None on confirmed success.

    client provides the S3 request contract. The dedicated bucket must have
    no objects or multipart uploads and no concurrent external writers. Check
    both listings, then conditionally create the control object; never replace
    existing state. Inspection or creation failures raise Stop (malformed XML
    raises ParseError); an uncertain write must be inspected before retrying.
    """
    # Explicit one-time initialization ONLY for a verified empty dedicated bucket.
    for query, forbidden, expected in [({'list-type': '2', 'max-keys': '1'}, 'Contents', 'ListBucketResult'),
                             ({'uploads': '', 'max-uploads': '1'}, 'Upload', 'ListMultipartUploadsResult')]:
        code, body, _ = client.request('GET', query=query)
        if code != 200:
            raise Stop('cannot inspect bucket before initialization')
        root = ET.fromstring(body)
        if root.tag.rsplit('}', 1)[-1] != expected:
            raise Stop('unexpected bucket inspection response')
        if any(e.tag.rsplit('}', 1)[-1] == forbidden or
               (e.tag.rsplit('}', 1)[-1] == 'IsTruncated' and e.text != 'false')
               for e in root.iter()):
            raise Stop('initialization requires an empty bucket with no multipart uploads')
    state = initial_state()
    state.update(day=dt.datetime.now(dt.timezone.utc).date().isoformat(), class_a=3)
    code, _, _ = client.request('PUT', STATE_KEY, json.dumps(state).encode(),
                                {'If-None-Match': '*'})
    if code != 200:
        raise Stop('budget already exists or initialization failed')


def _observed_budget(body, headers):
    """Charge a completed reservation through the control object's server day.

    A PUT may commit after midnight even if its body was prepared before it.
    Its server-controlled Last-Modified and ETag describe the same GET version.
    Carry the entire previous reservation forward to that UTC day before any
    reset. This overcounts safely, including initialization and completion PUTs,
    without another write or a change to the persisted state format. Missing or
    invalid metadata stops admission; a locked state still cannot be reused.
    """
    try:
        modified = parsedate_to_datetime(headers['last-modified'])
        if modified.tzinfo is None:
            raise ValueError('missing timezone')
        server_day = modified.astimezone(dt.timezone.utc).date().isoformat()
    except (KeyError, TypeError, ValueError, OverflowError) as error:
        raise Stop('budget Last-Modified missing or invalid; no upload') from error
    state = json.loads(body)
    if not isinstance(state, dict) or not isinstance(state.get('day'), str):
        raise Stop('invalid budget state')
    state['day'] = max(state['day'], server_day)
    return state


def publish(client, objects, today=None):
    """Publish a validated frozen plan, returning None on confirmed completion.

    objects must be the nonempty ordered sequence returned by load_plan, with
    the revision map last and files unchanged. client provides S3.request and
    server-controlled last-modified plus etag headers on the budget GET;
    today optionally supplies the UTC ISO date, otherwise the current date is
    used. Persist a conditional budget reservation before payload PUTs, upload
    artifacts before the map, then conditionally clear the lock. Failures raise
    Stop or propagate parsing/file errors. After reservation, failure retains
    the byte/operation budget and may leave a lock or partial remote uploads;
    never automatically retry, refund, or clear an uncertain reservation.
    """
    today = today or dt.datetime.now(dt.timezone.utc).date().isoformat()
    code, body, headers = client.request('GET', STATE_KEY)
    if code != 200 or 'etag' not in headers:
        raise Stop('budget missing or unreadable; never initialize implicitly')
    state = reserve(_observed_budget(body, headers),
                    [p.stat().st_size for _, p in objects], today, uuid.uuid4().hex)
    code, _, headers = client.request('PUT', STATE_KEY, json.dumps(state).encode(),
                                      {'If-Match': headers['etag']})
    if code != 200 or 'etag' not in headers:
        raise Stop('budget reservation failed or concurrent publisher; no upload')
    reservation_etag = headers['etag']
    def upload(item):
        key, path = item
        # A run crossing midnight stops, retaining its conservative reservation.
        if dt.datetime.now(dt.timezone.utc).date().isoformat() != today:
            raise Stop('UTC date changed during publication; inspection required')
        content = 'application/vnd.reservoir.outputs+json-lines' if MAP.fullmatch(key) else 'application/vnd.reservoir.artifact'
        code, _, _ = client.request('PUT', key, path, {'Content-Type': content})
        if code != 200:
            raise Stop('upload failed; reservation retained; no automatic retry')
    # Bounded parallelism for artifacts, with the revision map strictly last.
    # All submitted operations have already been reserved, including on failure.
    with ThreadPoolExecutor(max_workers=16) as pool:
        for _ in pool.map(upload, objects[:-1]):
            pass
    upload(objects[-1])
    state['active'] = None
    code, _, _ = client.request('PUT', STATE_KEY, json.dumps(state).encode(),
                                {'If-Match': reservation_etag})
    if code != 200:
        raise Stop('completion uncertain; reservation retained; inspection required')


def adopt_existing(client):
    """Conservatively add existing bucket bytes to the budget; never refund.

    Administrative operation only: stop every external writer first. Refuse
    active reservations and pending multipart uploads. Reserve 23 operations
    (two state PUTs, one multipart listing, at most twenty object pages), lock
    with If-Match, then add the inventory bytes to the existing reservation.
    Double counting is intentional. Any uncertain or incomplete inventory
    leaves the lock in place. Historical unguarded operations are not covered
    retroactively. Return None after a confirmed conditional completion PUT.
    """
    today = dt.datetime.now(dt.timezone.utc).date().isoformat()
    code, body, headers = client.request('GET', STATE_KEY)
    if code != 200 or 'etag' not in headers:
        raise Stop('budget missing or unreadable')
    state = reserve(_observed_budget(body, headers), [0] * 21, today, uuid.uuid4().hex)
    code, _, headers = client.request('PUT', STATE_KEY, json.dumps(state).encode(),
                                      {'If-Match': headers['etag']})
    if code != 200 or 'etag' not in headers:
        raise Stop('inventory reservation failed; no inventory started')
    etag = headers['etag']

    def listing(query, expected):
        if dt.datetime.now(dt.timezone.utc).date().isoformat() != today:
            raise Stop('UTC date changed during inventory; inspection required')
        code, body, _ = client.request('GET', query=query)
        if code != 200:
            raise Stop('inventory listing failed; reservation retained')
        root = ET.fromstring(body)
        for element in root.iter():
            element.tag = element.tag.rsplit('}', 1)[-1]
        if root.tag != expected:
            raise Stop('unexpected inventory response')
        return root

    root = listing({'uploads': '', 'max-uploads': '1'}, 'ListMultipartUploadsResult')
    if root.findall('Upload') or root.findtext('IsTruncated') != 'false':
        raise Stop('pending multipart uploads; inspection required')
    total, token, seen = 0, None, set()
    for _ in range(20):
        query = {'list-type': '2', 'max-keys': '1000'}
        if token:
            query['continuation-token'] = token
        root = listing(query, 'ListBucketResult')
        for obj in root.findall('Contents'):
            key, size = obj.findtext('Key'), obj.findtext('Size')
            if not key or key in seen or not size or not size.isdecimal():
                raise Stop('invalid or duplicate inventory entry')
            seen.add(key)
            if key != STATE_KEY:
                total += int(size)
            if state['reserved_bytes'] + total > LIMIT:
                raise Stop('inventory exceeds conservative storage budget')
        if root.findtext('IsTruncated') == 'false':
            break
        if root.findtext('IsTruncated') != 'true':
            raise Stop('invalid inventory pagination')
        next_token = root.findtext('NextContinuationToken')
        if not next_token or next_token == token:
            raise Stop('missing or repeated inventory continuation token')
        token = next_token
    else:
        raise Stop('inventory page limit reached; reservation retained')
    if STATE_KEY not in seen:
        raise Stop('budget absent from inventory; inspection required')
    state.update(reserved_bytes=state['reserved_bytes'] + total, active=None)
    code, _, _ = client.request('PUT', STATE_KEY, json.dumps(state).encode(), {'If-Match': etag})
    if code != 200:
        raise Stop('inventory completion uncertain; inspection required')
    print(f'Existing payload bytes added to reservation: {total}')


def main():
    """Run explicit budget administration or publish from CLI and environment.

    Read MEI_R2_BUCKET_ENDPOINT and LAKE_CACHE_KEY_RAW; publish also requires
    --plan pointing to a trusted frozen plan. Return None and print success
    only after the selected operation completes. Exceptions propagate to the
    entrypoint, which reports failure and exits with status 2 for handled errors.
    """
    parser = argparse.ArgumentParser()
    parser.add_argument('command', choices=['initialize-empty', 'adopt-existing', 'publish'])
    parser.add_argument('--plan', type=Path)
    args = parser.parse_args()
    endpoint = os.environ['MEI_R2_BUCKET_ENDPOINT'].rstrip('/')
    objects = load_plan(args.plan, endpoint) if args.command == 'publish' else None
    client = S3(endpoint, os.environ['LAKE_CACHE_KEY_RAW'].strip())
    if args.command == 'adopt-existing':
        adopt_existing(client)
    elif objects is None:
        initialize(client)
    else:
        publish(client, objects)
    print('R2 ' + args.command + ' succeeded')


if __name__ == '__main__':
    try:
        main()
    except (Stop, ValueError, OSError, KeyError, ET.ParseError) as error:
        # Never print credential-bearing requests or backend response bodies.
        print('R2 publication stopped: ' + str(error))
        raise SystemExit(2)
