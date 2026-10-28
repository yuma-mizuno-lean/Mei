#!/usr/bin/env python3
"""Transport stock Lake stage/unstage archives through public GitHub Releases.

Only audited main builds publish. No candidate script or download receives a token.
This transports platform-independent Lake mappings, not a copied .lake/build tree.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile
import time
import urllib.error
import urllib.request

REPO = "yuma-mizuno-lean/Mei"
FORMAT = 1
MAX_BUNDLE = 1900 * 1024**2  # below GitHub's per-asset 2 GiB limit
MAX_EXPANDED = 8 * 1024**3
ARCHIVE = re.compile(r"[0-9a-f]{16}\.ltar")
REVISION = re.compile(r"[0-9a-f]{40}")
INPUTS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")


def run(args, cwd, env=None):
    return subprocess.run(args, cwd=cwd, env=env, check=True,
                          text=True, stdout=subprocess.PIPE).stdout.strip()


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def identity(root):
    # Source edits need not match: Lake's per-target input hashes determine reuse.
    # Configuration/pins must match; never execute a candidate lakefile.lean here.
    if (root / "lakefile.lean").exists():
        raise ValueError("only declarative lakefile.toml is supported")
    import tomllib
    config = tomllib.loads((root / "lakefile.toml").read_text())
    if config.get("platformIndependent") is not True:
        raise ValueError("platformIndependent=true required")
    if config.get("fixedToolchain") or config.get("bootstrap"):
        raise ValueError("toolchain scope must not be disabled")
    return {name: digest(root / name) for name in INPUTS}


def tag_for(inputs):
    key = hashlib.sha256(json.dumps(inputs, sort_keys=True).encode()).hexdigest()
    return "mei-cache-v1-" + key


def mappings(raw):
    if len(raw) > 16 * 1024**2:
        raise ValueError("map too large")
    rows = [json.loads(line) for line in raw.splitlines() if line.strip()]
    if not rows or rows[0] != "2026-03-17":
        raise ValueError("unsupported Lake map version")
    inputs, archives = set(), set()
    for row in rows[1:]:
        if (not isinstance(row, list) or len(row) != 2
                or not isinstance(row[0], str) or not re.fullmatch(r"[0-9a-f]{16}", row[0])
                or not isinstance(row[1], str) or not ARCHIVE.fullmatch(row[1])
                or row[0] in inputs):
            raise ValueError("invalid Lake mapping")
        inputs.add(row[0])
        archives.add(row[1])
    if not archives:
        raise ValueError("empty Lake map")
    return archives


def pack(root, stage, output):
    inputs = identity(root)
    revision = run(["git", "rev-parse", "HEAD"], root)
    if not REVISION.fullmatch(revision):
        raise ValueError("invalid revision")
    names = mappings((stage / "outputs.jsonl").read_bytes()) | {"outputs.jsonl"}
    if {p.name for p in stage.iterdir()} != names:
        raise ValueError("stage must contain only stock Lake outputs")
    records = {}
    for name in sorted(names):
        p = stage / name
        if p.is_symlink() or not p.is_file():
            raise ValueError("stage contains nonregular file")
        records[name] = {"size": p.stat().st_size, "sha256": digest(p)}
    if sum(r["size"] for r in records.values()) > MAX_EXPANDED:
        raise ValueError("cache exceeds expansion limit")
    meta = {"format": FORMAT, "repository": REPO, "revision": revision,
            "inputs": inputs, "files": records}
    output.mkdir(parents=True, exist_ok=True)
    bundle = output / (revision + ".tar.gz")
    with tarfile.open(bundle, "w:gz", compresslevel=1) as tf:
        for name in sorted(names):
            tf.add(stage / name, arcname=name, recursive=False)
    if bundle.stat().st_size > MAX_BUNDLE:
        raise ValueError("bundle exceeds free release asset size limit")
    meta.update(bundle=bundle.name, bundle_sha256=digest(bundle),
                bundle_size=bundle.stat().st_size, tag=tag_for(inputs))
    (output / "manifest.json").write_text(json.dumps(meta, sort_keys=True) + "\n")
    print(json.dumps({"tag": meta["tag"], "revision": revision,
                      "bytes": meta["bundle_size"], "archives": len(names) - 1}))


def unpack(bundle, meta, destination, expected):
    if (meta.get("format") != FORMAT or meta.get("repository") != REPO
            or meta.get("inputs") != expected
            or not REVISION.fullmatch(meta.get("revision", ""))
            or meta.get("tag") != tag_for(expected)
            or meta.get("bundle") != meta["revision"] + ".tar.gz"):
        raise ValueError("cache identity mismatch")
    if bundle.stat().st_size > MAX_BUNDLE or digest(bundle) != meta["bundle_sha256"]:
        raise ValueError("bundle checksum mismatch")
    records = meta["files"]
    if not isinstance(records, dict) or "outputs.jsonl" not in records:
        raise ValueError("missing map")
    if any(name != "outputs.jsonl" and not ARCHIVE.fullmatch(name) for name in records):
        raise ValueError("unsafe filename")
    total = sum(r["size"] for r in records.values())
    if total < 0 or total > MAX_EXPANDED:
        raise ValueError("invalid expanded size")
    destination.mkdir()
    with tarfile.open(bundle, "r:gz") as tf:
        seen = set()
        for member in tf:
            name = member.name
            if name not in records or name in seen or not member.isfile():
                raise ValueError("unexpected archive member")
            if member.size != records[name]["size"] or member.size < 0:
                raise ValueError("member size mismatch")
            seen.add(name)
            with tf.extractfile(member) as src, (destination / name).open("xb") as dst:
                shutil.copyfileobj(src, dst)
            if digest(destination / name) != records[name]["sha256"]:
                raise ValueError("member checksum mismatch")
    if seen != set(records):
        raise ValueError("missing archive members")
    if mappings((destination / "outputs.jsonl").read_bytes()) != seen - {"outputs.jsonl"}:
        raise ValueError("map/archive mismatch")


def download(url, target, limit):
    # Public endpoints only. Never forward an ambient GitHub/S3 credential.
    request = urllib.request.Request(url, headers={"User-Agent": "Mei-Lake-cache/1"})
    with urllib.request.urlopen(request, timeout=60) as response, target.open("wb") as out:
        size = 0
        while chunk := response.read(1024 * 1024):
            size += len(chunk)
            if size > limit:
                raise ValueError("download exceeds limit")
            out.write(chunk)


def restore(root):
    started = time.monotonic()
    inputs = identity(root)
    tag = tag_for(inputs)
    # One compatibility tag, commit-named immutable payloads, manifest published last.
    base = f"https://github.com/{REPO}/releases/download/{tag}/"
    cache = root / ".lake" / "cache"
    env = dict(os.environ, LAKE_ARTIFACT_CACHE="true", LAKE_RESTORE_ARTIFACTS="true",
               LAKE_CACHE_DIR=str(cache), LAKE_NO_CACHE="true")
    with tempfile.TemporaryDirectory(prefix="mei-release-cache-") as tmp:
        tmp = Path(tmp)
        download(base + "manifest.json", tmp / "manifest.json", 16 * 1024**2)
        meta = json.loads((tmp / "manifest.json").read_text())
        rev = meta.get("revision", "")
        if not REVISION.fullmatch(rev):
            raise ValueError("invalid release revision")
        bundle = tmp / "bundle.tar.gz"
        download(base + rev + ".tar.gz", bundle, MAX_BUNDLE)
        unpack(bundle, meta, tmp / "stage", inputs)
        run(["lake", "cache", "unstage", str(tmp / "stage"), "--force-overwrite"], root, env)
    if os.environ.get("GITHUB_ENV"):
        with open(os.environ["GITHUB_ENV"], "a") as f:
            for k in ("LAKE_ARTIFACT_CACHE", "LAKE_RESTORE_ARTIFACTS", "LAKE_CACHE_DIR"):
                f.write(f"{k}={env[k]}\n")
    print(f"Mei cache restored: source={rev}, seconds={time.monotonic()-started:.1f}")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("command", choices=["pack", "restore", "validate"])
    p.add_argument("project", type=Path)
    p.add_argument("--stage", type=Path)
    p.add_argument("--output", type=Path)
    a = p.parse_args()
    root = a.project.resolve()
    if a.command == "pack":
        pack(root, a.stage, a.output)
    elif a.command == "validate":
        meta = json.loads((a.stage / "manifest.json").read_text())
        with tempfile.TemporaryDirectory() as tmp:
            # This job checks out the exact audited producer revision independently.
            if meta.get("revision") != run(["git", "rev-parse", "HEAD"], root):
                raise ValueError("producer revision mismatch")
            if (not REVISION.fullmatch(meta.get("revision", ""))
                    or meta.get("bundle") != meta["revision"] + ".tar.gz"):
                raise ValueError("invalid bundle name")
            unpack(a.stage / meta["bundle"], meta, Path(tmp) / "stage", identity(root))
        print("Release cache validated")
    else:
        try:
            restore(root)
        except (OSError, ValueError, KeyError, subprocess.CalledProcessError,
                tarfile.TarError, urllib.error.URLError) as e:
            print(f"Mei cache unavailable; normal build retained: {e}")
            return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
