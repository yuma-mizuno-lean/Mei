# CI cache transport

Main CI, PR/merge-group builds and full lint restore one GitHub Actions cache
archive containing Mei's standard Lake output records and compressed `.ltar`
artifacts. `services.cache.ci_bundle = true` preserves the PR setting when Tools
regenerates the wrapper. The customized main/full-lint workflows use the same
pinned restore action.

Only successful main builds save this cache; candidate builds only read it.
Keys include OS, architecture, Lean toolchain and the publishing revision.
Prefix restoration supplies older artifacts; Lake's input hashes determine
which are reusable. Changed or missing modules compile locally. There is no
fallback to individual Mei Cloudflare downloads or revision-history searches.
This is one archive transfer, not a promise of one HTTP request to GitHub.

The transport helper rejects unsafe paths, mismatched toolchains and corrupted
files before installing records. The archive is limited to 64 MiB. A separate
job retains eight generations (at most 512 MiB, plus one transient generation).
Saving is skipped when the repository's measured total plus the new archive
would exceed 8 GiB. This is an operational bound, not an account-wide billing
cap; other workflows and repositories have their own usage.

CI needs zero requests to the Mei Cloudflare reader for restoration. Mathlib
and TauCeti continue using their independently operated upstream caches.
Keep the Mei reader disabled and MEI_R2_GUARDS_READY unset during this rollout;
the existing public R2 publisher remains dormant. Public distribution to other
users is a separate path, not enabled by the GitHub Actions cache.

Validation requires both a cold main run that saves the bundle and a subsequent
run that reports a GitHub cache hit and Lake unpacking unchanged modules. A
cache miss may take one full compilation. Unit tests alone do not prove CI
integration or account-wide daily request usage.
