import datetime as dt
from email.utils import format_datetime
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from mei_r2_publish import A_LIMIT, LIMIT, STATE_ALLOWANCE, STATE_KEY, Stop, adopt_existing, initial_state, initialize, load_plan, publish, reserve

TODAY = dt.datetime.now(dt.timezone.utc).date().isoformat()


class FakeR2:
    def __init__(self, fail_key=None, conflict=False, now=None, initialized=True):
        self.state = initial_state()
        self.etag = '0'
        self.calls = []
        self.fail_key, self.conflict = fail_key, conflict
        self.now = now or (lambda: dt.datetime.now(dt.timezone.utc))
        self.modified = self.now()
        self.initialized = initialized
        self.before_put = None

    def request(self, method, key='', data=None, headers=None, query=None):
        self.calls.append((method, key))
        if query is not None:
            root = 'ListBucketResult' if 'list-type' in query else 'ListMultipartUploadsResult'
            return 200, f'<{root}><IsTruncated>false</IsTruncated></{root}>'.encode(), {}
        if method == 'PUT' and self.before_put is not None:
            self.before_put(key, data, headers)
        if key == STATE_KEY:
            if method == 'GET':
                return 200, json.dumps(self.state).encode(), {
                    'etag': self.etag,
                    'last-modified': format_datetime(self.modified, usegmt=True),
                }
            create = headers.get('If-None-Match') == '*'
            if self.conflict or (self.initialized if create else headers.get('If-Match') != self.etag):
                return 412, b'', {}
            self.state = json.loads(data)
            self.etag = str(int(self.etag) + 1)
            self.modified = self.now()
            self.initialized = True
            return 200, b'', {'etag': self.etag}
        if key == self.fail_key:
            raise Stop('unknown transport outcome')
        return 200, b'', {}


class BudgetTests(unittest.TestCase):
    def inventory_client(self, pages, multipart=False):
        client = FakeR2()
        request = client.request
        def inventory(method, key='', data=None, headers=None, query=None):
            if query and 'list-type' in query:
                return 200, pages.pop(0).encode(), {}
            if query and multipart:
                return 200, b'<ListMultipartUploadsResult><Upload/><IsTruncated>false</IsTruncated></ListMultipartUploadsResult>', {}
            return request(method, key, data, headers, query)
        client.request = inventory
        return client

    def test_inventory_counts_all_pages_without_refunds(self):
        pages = [
            '<ListBucketResult><Contents><Key>_control/budget.json</Key><Size>100</Size></Contents><Contents><Key>a</Key><Size>11</Size></Contents><IsTruncated>true</IsTruncated><NextContinuationToken>next</NextContinuationToken></ListBucketResult>',
            '<ListBucketResult><Contents><Key>b</Key><Size>22</Size></Contents><IsTruncated>false</IsTruncated></ListBucketResult>',
        ]
        client = self.inventory_client(pages)
        client.state['reserved_bytes'] += 50
        adopt_existing(client)
        self.assertEqual(client.state['reserved_bytes'], STATE_ALLOWANCE + 50 + 33)
        self.assertEqual(client.state['class_a'], 23)
        self.assertIsNone(client.state['active'])

    def test_inventory_overflow_and_multipart_keep_lock(self):
        for pages, multipart in [
            ([f'<ListBucketResult><Contents><Key>a</Key><Size>{LIMIT}</Size></Contents><IsTruncated>false</IsTruncated></ListBucketResult>'], False),
            ([], True),
            (['<ListBucketResult><IsTruncated>true</IsTruncated></ListBucketResult>'], False),
        ]:
            with self.subTest(pages=pages, multipart=multipart):
                client = self.inventory_client(pages, multipart)
                with self.assertRaises(Stop):
                    adopt_existing(client)
                self.assertIsNotNone(client.state['active'])
                self.assertEqual(client.state['reserved_bytes'], STATE_ALLOWANCE)

    def test_inventory_conflict_does_not_list(self):
        client = FakeR2(conflict=True)
        with self.assertRaises(Stop):
            adopt_existing(client)
        self.assertNotIn(('GET', ''), client.calls)

    def test_exact_capacity_and_one_byte_over(self):
        state = reserve(initial_state(), [LIMIT - STATE_ALLOWANCE], TODAY, 'token')
        self.assertEqual(state['reserved_bytes'], LIMIT)
        with self.assertRaises(Stop):
            reserve(initial_state(), [LIMIT - STATE_ALLOWANCE + 1], TODAY, 'token')

    def test_daily_budget_does_not_reset_on_rerun(self):
        state = initial_state()
        state.update(day=TODAY, class_a=A_LIMIT - 3)
        next_state = reserve(state, [1], TODAY, 'token')
        next_state['active'] = None
        with self.assertRaises(Stop):
            reserve(next_state, [1], TODAY, 'another')
        next_state['day'] = '2000-01-01'
        self.assertEqual(reserve(next_state, [1], TODAY, 'another')['class_a'], 3)

    def test_prior_interruption_never_unlocks_automatically(self):
        state = reserve(initial_state(), [10], '2000-01-01', 'old')
        with self.assertRaises(Stop):
            reserve(state, [10], TODAY, 'new')

    def test_upload_order_and_failure_reservation(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'payload'
            path.write_bytes(b'12345')
            objects = [('artifact', path), ('map', path)]
            client = FakeR2(fail_key='artifact')
            with self.assertRaises(Stop):
                publish(client, objects)
            self.assertIsNotNone(client.state['active'])
            self.assertEqual(client.state['reserved_bytes'], STATE_ALLOWANCE + 10)
            self.assertNotIn(('PUT', 'map'), client.calls)
            with self.assertRaises(Stop):
                publish(client, objects)
            self.assertEqual(client.calls.count(('PUT', 'artifact')), 1)

    def test_concurrent_reservation_loser_never_uploads(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'payload'
            path.write_bytes(b'x')
            client = FakeR2(conflict=True)
            with self.assertRaises(Stop):
                publish(client, [('artifact', path)])
            self.assertNotIn(('PUT', 'artifact'), client.calls)

    def test_success_unlocks_but_retains_reserved_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'payload'
            path.write_bytes(b'x')
            client = FakeR2()
            publish(client, [('artifact', path), ('map', path)])
            self.assertIsNone(client.state['active'])
            self.assertEqual(client.state['class_a'], 4)
            self.assertEqual(client.calls[2:4], [('PUT', 'artifact'), ('PUT', 'map')])

    def test_midnight_writes_remain_charged_on_their_server_day(self):
        # A request can begin before midnight and commit after it. Exercise
        # actual publication and initialization, including the next admission.
        for boundary in ('final-map', 'completion', 'initialization'):
            with self.subTest(boundary=boundary), tempfile.TemporaryDirectory() as tmp:
                old = dt.datetime(2026, 10, 28, 23, 59, 59, tzinfo=dt.timezone.utc)
                new = old + dt.timedelta(seconds=2)
                clock = SimpleNamespace(current=old)
                fake_dt = SimpleNamespace(
                    datetime=SimpleNamespace(now=lambda tz: clock.current),
                    timezone=dt.timezone,
                )
                client = FakeR2(now=lambda: clock.current,
                                initialized=boundary != 'initialization')

                def rollover(key, data, headers):
                    completion = key == STATE_KEY and json.loads(data)['active'] is None
                    if ((boundary == 'final-map' and key == 'map')
                            or (boundary == 'completion' and completion)
                            or (boundary == 'initialization' and key == STATE_KEY)):
                        clock.current = new

                client.before_put = rollover
                path = Path(tmp) / 'payload'
                path.write_bytes(b'x')
                with patch('mei_r2_publish.dt', fake_dt):
                    if boundary == 'initialization':
                        initialize(client)
                    else:
                        publish(client, [('artifact', path), ('map', path)])
                    self.assertIsNone(client.state['active'])
                    self.assertEqual(client.state['day'], old.date().isoformat())
                    self.assertEqual(client.modified, new)
                    previous_cost = client.state['class_a']
                    before = len([c for c in client.calls if c[0] == 'PUT'])
                    full_day = [(f'artifact-{i}', path) for i in range(A_LIMIT - 3)]
                    full_day.append(('map', path))
                    with self.assertRaises(Stop):
                        publish(client, full_day)
                    self.assertEqual(len([c for c in client.calls if c[0] == 'PUT']), before)
                    client.before_put = None
                    publish(client, [('map', path)])
                    self.assertEqual(client.state['class_a'], previous_cost + 3)

    def test_daily_budget_resets_after_the_last_control_write_day(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'payload'
            path.write_bytes(b'x')
            client = FakeR2()
            client.state.update(day='2000-01-01', class_a=A_LIMIT)
            client.modified = dt.datetime(2000, 1, 2, tzinfo=dt.timezone.utc)
            publish(client, [('map', path)])
            self.assertEqual(client.state['class_a'], 3)

    def test_unusable_server_timestamp_stops_before_any_put(self):
        for stamp in (None, '', 'invalid', 'Thu, 29 Oct 2026 00:00:00 -0000',
                      'Mon, 01 Jan 2099 00:00:00 GMT'):
            with self.subTest(stamp=stamp), tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / 'payload'
                path.write_bytes(b'x')
                client = FakeR2()
                original_request = client.request

                def request(*args, **kwargs):
                    code, body, headers = original_request(*args, **kwargs)
                    if args[0] == 'GET':
                        if stamp is None:
                            headers.pop('last-modified')
                        else:
                            headers['last-modified'] = stamp
                    return code, body, headers

                client.request = request
                with self.assertRaises(Stop):
                    publish(client, [('map', path)])
                self.assertFalse(any(method == 'PUT' for method, _ in client.calls))

    def test_plan_rejects_external_url_and_preserves_map_last(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            endpoint = 'https://' + 'a' * 32 + '.r2.cloudflarestorage.com/mei-cache'
            name = '0123456789abcdef'
            path = root / (name + '.ltar')
            path.write_bytes(b'x')
            (root / 'outputs.jsonl').write_text('map')
            (root / 'map-url').write_text(endpoint + '/revisions/yuma-mizuno-lean/Mei/tc/leanprover--lean4---v4.36.0/' + 'b' * 40 + '.jsonl')
            config = 'upload-file = ' + json.dumps(str(path)) + '\nurl = ' + json.dumps(endpoint + '/artifacts/yuma-mizuno-lean/Mei/' + name + '.art') + '\n'
            (root / 'artifacts.curl').write_text(config)
            objects = load_plan(root, endpoint)
            self.assertEqual(objects[-1][1].name, 'outputs.jsonl')
            (root / 'artifacts.curl').write_text(config.replace(endpoint, 'https://evil.example'))
            with self.assertRaises(Stop):
                load_plan(root, endpoint)


if __name__ == '__main__':
    unittest.main()
