#!/usr/bin/env python3
"""Opt-in WSL Lake launcher; install next to a trusted mei_release_cache.py.

Use a private PATH directory, never replace elan itself. Only Mei builds are affected.
Missing release caches remain nonfatal; each checkout is probed at most once/hour
for the same commit. Existing compiled outputs and ongoing worker rounds are kept.
"""
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

real = os.environ.get("MEI_REAL_LAKE", str(Path.home() / ".elan/bin/lake"))
env = dict(os.environ)
if "build" in sys.argv[1:] and env.get("MEI_RELEASE_CACHE") == "1":
    try:
        root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
        remote = subprocess.check_output(["git", "remote", "get-url", "origin"], cwd=root, text=True).strip()
        if remote.rstrip("/").removesuffix(".git") in {
            "https://github.com/yuma-mizuno-lean/Mei", "https://github.com/yuma-mizuno/Mei",
            "git@github.com:yuma-mizuno-lean/Mei", "git@github.com:yuma-mizuno/Mei",
        }:
            lake_dir = root / ".lake"
            lake_dir.mkdir(exist_ok=True)
            # Follow neither checkout-controlled lock/marker links nor another worker's output.
            fd = os.open(lake_dir / "mei-release.lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
            with os.fdopen(fd, "w") as lock:
                fcntl.flock(lock, fcntl.LOCK_EX)
                head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
                marker = lake_dir / "mei-release-probe.json"
                previous = {}
                if marker.is_file() and not marker.is_symlink():
                    previous = json.loads(marker.read_text())
                env.update(LAKE_ARTIFACT_CACHE="true", LAKE_RESTORE_ARTIFACTS="true",
                           LAKE_CACHE_DIR=str(lake_dir / "cache"))
                if previous.get("head") != head or time.time() - previous.get("at", 0) > 3600:
                    helper_env = dict(env)
                    # Restore invokes real Lake, never this launcher recursively.
                    helper_env["PATH"] = str(Path(real).parent) + os.pathsep + env.get("PATH", "")
                    rc = subprocess.run([sys.executable, str(Path(__file__).with_name("mei_release_cache.py")),
                                         "restore", str(root)], env=helper_env, timeout=300).returncode
                    tmp = marker.with_suffix(".tmp")
                    fd = os.open(tmp, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
                    with os.fdopen(fd, "w") as out:
                        json.dump({"head": head, "at": time.time(), "result": rc}, out)
                    os.replace(tmp, marker)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Mei cache preparation deferred; continuing build: {error}", file=sys.stderr)
os.execve(real, [real, *sys.argv[1:]], env)
