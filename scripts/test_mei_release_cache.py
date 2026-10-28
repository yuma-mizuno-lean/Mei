#!/usr/bin/env python3
"""Unit and actual-Lake round trip / changed-source regression tests."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import mei_release_cache as cache


class Transport(unittest.TestCase):
    def test_map_rejects_paths_and_duplicates(self):
        for rows in [[], ["bad"], ["2026-03-17", ["a"*16, "../x"]],
                     ["2026-03-17", ["a"*16, "b"*16+".ltar"],
                      ["a"*16, "c"*16+".ltar"]]]:
            with self.assertRaises(ValueError):
                cache.mappings("\n".join(map(json.dumps, rows)).encode())

    @unittest.skipUnless(os.environ.get("MEI_CACHE_INTEGRATION") == "1", "actual Lake opt-in")
    def test_stock_lake_round_trip(self):
        with tempfile.TemporaryDirectory(prefix="mei-cache-test-") as tmp:
            root = Path(tmp)
            producer, consumer = root / "producer", root / "consumer"
            producer.mkdir()
            (producer / "lakefile.toml").write_text('name = "Probe"\nplatformIndependent = true\ndefaultTargets = ["Probe"]\n[[lean_lib]]\nname = "Probe"\n')
            (producer / "lean-toolchain").write_text(os.environ["ELAN_TOOLCHAIN"] + "\n")
            (producer / "Probe.lean").write_text('def answer : Nat := 42\n')
            env = dict(os.environ, LAKE_ARTIFACT_CACHE="true", LAKE_RESTORE_ARTIFACTS="true",
                       LAKE_NO_CACHE="true", LAKE_CACHE_DIR=str(root / "producer-cache"))
            cache.run(["lake", "build", "-o", "outputs.jsonl"], producer, env)
            cache.run(["git", "init", "-q"], producer)
            cache.run(["git", "add", "lakefile.toml", "lean-toolchain", "lake-manifest.json", "Probe.lean"], producer)
            cache.run(["git", "-c", "user.name=Cache test", "-c", "user.email=test@example.invalid",
                       "commit", "-qm", "fixture"], producer)
            cache.run(["lake", "cache", "stage", "outputs.jsonl", str(root / "stage")], producer, env)
            cache.pack(producer, root / "stage", root / "upload")
            meta = json.loads((root / "upload/manifest.json").read_text())
            bundle = root / "upload" / meta["bundle"]
            cache.unpack(bundle, meta, root / "unpacked", cache.identity(producer))
            cache.run(["git", "clone", "-q", str(producer), str(consumer)], root)
            env["LAKE_CACHE_DIR"] = str(root / "consumer-cache")
            cache.run(["lake", "cache", "unstage", str(root / "unpacked")], consumer, env)
            result = cache.run(["lake", "build"], consumer, env)
            self.assertNotIn("Built Probe", result, result)
            print("UNCHANGED:", result)
            self.assertEqual(cache.digest(producer / ".lake/build/lib/lean/Probe.olean"),
                             cache.digest(consumer / ".lake/build/lib/lean/Probe.olean"))
            (consumer / "Probe.lean").write_text('def answer : Nat := 43\n')
            result = cache.run(["lake", "build"], consumer, env)
            self.assertIn("Built Probe", result)
            cached = cache.digest(consumer / ".lake/build/lib/lean/Probe.olean")
            print("CHANGED:", result)
            shutil.rmtree(consumer / ".lake/build")
            cold_env = dict(env, LAKE_ARTIFACT_CACHE="false", LAKE_RESTORE_ARTIFACTS="false")
            cache.run(["lake", "build"], consumer, cold_env)
            self.assertEqual(cached, cache.digest(consumer / ".lake/build/lib/lean/Probe.olean"))
            bad = dict(meta, bundle_sha256="0"*64)
            with self.assertRaises(ValueError):
                cache.unpack(bundle, bad, root / "bad", cache.identity(producer))
            mismatch = dict(cache.identity(producer), **{"lean-toolchain": "0"*64})
            with self.assertRaises(ValueError):
                cache.unpack(bundle, meta, root / "mismatch", mismatch)
            print("COLD EQUIVALENCE, CORRUPTION AND PIN MISMATCH: passed")


if __name__ == "__main__":
    unittest.main()
