# Mei's shared build cache

Mei uses stock Lake output maps and `.ltar` artifacts, as the existing remote
Lake cache does. GitHub Releases is only the transport: it does not choose which
modules are reusable. `platformIndependent = true` is retained. Native executables
are excluded by Lake's platform-independent map; OS/CPU model matching is not
imposed on the library cache.

## Trust and publication

Enable repository variable `MEI_RELEASE_CACHE=1` after merging this infrastructure
change. The normal main CI builds and audits the source, then uses `lake build
--no-build --rehash -o ...` and `lake cache stage` to export its root-package
outputs. A separate job validates every archive and uploads to a prerelease.
Only that job has `contents: write`. PRs and merge groups only read; they never
publish. Downloads are anonymous and candidate code never receives a write key.

The compatibility tag hashes `lean-toolchain`, `lake-manifest.json`, and
`lakefile.toml`. Each payload is named by its producer commit; the manifest is
updated last. Source changes do not change the tag: stock Lake checks per-target
input hashes and recompiles affected targets. Pin/configuration changes cause a
cache miss until their main build is published. SHA-256 and bounded, regular-file
extraction reject corrupt bundles, unexpected paths, symlinks and incomplete maps.
These checks protect transport; source correctness still relies on the existing
build, axiom, module, lint and review gates.

Old payloads in the same compatibility scope are deleted after publication.
Older compatibility tags remain available to PRs with old dependency pins.
Release assets are bounded below 2 GiB. A transient Actions cache transfers between isolated jobs using an exact
run-specific key on main, then is deleted after publication. It shares the
existing 10 GB cache allowance; there is no Actions artifact-storage upload.
If publication fails, the ordinary cache eviction policy applies. No paid cache expansion, R2 service or additional token
is enabled by this change. Repository billing controls remain in force.

## Consumption

PR/merge-group CI restore before the ordinary offline build. Main deliberately
compiles Mei without its artifact cache and runs all audits before publication;
it remains an independent source verification rather than trusting its own cache. The PR hook
executes the workflow-pinned copy of `scripts/mei_release_cache.py`, never a
candidate's helper. A missing or damaged release is reported and falls back to
the normal build. Mathlib continues using its own `lake exe cache get`.

For a manual WSL checkout:

```sh
python3 scripts/mei_release_cache.py restore .
LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true \
  LAKE_CACHE_DIR="$PWD/.lake/cache" LAKE_NO_CACHE=true lake build
```

For managed workers, install reviewed copies of `mei_worker_lake.py` (as `lake`)
and `mei_release_cache.py` together in a private executable PATH directory and
set `MEI_RELEASE_CACHE=1`. The launcher affects only Mei repositories, probes
once per commit/hour, serializes preparation within a checkout, then executes
the real elan Lake. Do not replace elan or restart an active worker merely to
install this optional acceleration. Enable it for subsequent rounds after the
first audited cache has been published and restored successfully.

## Verification

`MEI_CACHE_INTEGRATION=1 ELAN_TOOLCHAIN=$(cat lean-toolchain) python3
scripts/test_mei_release_cache.py` exercises actual Lake stage/unstage, proves
an unchanged source is unpacked rather than compiled, proves edited source is
rebuilt, and compares the edited result with a cold build. It also rejects
corruption and mismatched pins. This runs in CI as well as locally.

Deployment acceptance additionally requires a real main publication, a PR or
merge-group restore log naming that revision, and a WSL restore. Record timings
and archive bytes from those runs; a synthetic test alone does not establish the
speedup on Mei's full library.
