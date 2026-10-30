# Mei public Lake cache reader

## One writer, shared readers

Main CI is the only R2 writer and uses the guarded local publisher. CI restores
one GitHub Actions bundle and never reads individual Mei objects from this reader.
Host workers opt in separately with `services.cache.worker_public = true` and
use standard `lake cache get`; external users can use the same public service.
The host retains verified archives and revision maps between workers and rounds.
A root cache outage falls back to local building, without immediate retry.

Keep `LAKE_CACHE_ARTIFACT_ENDPOINT` and `LAKE_CACHE_REVISION_ENDPOINT` unset:
those legacy variables enable the shared Tools publisher, which does not use
Mei's budget guard. Main derives its write URLs from `MEI_R2_BUCKET_ENDPOINT`.
Queue acceptance requires the normal build and audits; publication follows
merge. A miss falls back to building normally.

## What is implemented

`worker.mjs` serves the existing TauCetiTools/Lake object paths, anonymously:

- `/artifacts/yuma-mizuno-lean/Mei/<16 lowercase hex>.art`
- `/revisions/yuma-mizuno-lean/Mei/tc/<escaped toolchain>/<40 lowercase hex>.jsonl`

GET or HEAD performs at most one R2 operation, including errors. All other
methods, paths, query strings, and Range requests are rejected before R2 access.
There is no upload, listing, proxy, recursion, retry, or scheduled handler.
Object bodies are streamed, not buffered. No S3 secret is needed for the reader.

The default `ENABLED=false` returns 503 without touching R2. It is intentionally
not controlled by a remotely accessible admin endpoint.

Run the local tests with:

```sh
node --test infra/mei-cache-reader/worker.test.mjs
```

These tests do not verify Cloudflare quotas, an actual R2 binding, deployed
behavior, or a complete `lake cache get` execution.

## Deployment prerequisites (all required)

1. Verify the actual Cloudflare account is on **Workers Free**, not Workers Paid.
   The daily 100,000 request cap is an account property, not enforced by Wrangler.
2. Verify `mei-cache` uses Standard storage. Keep R2 public development URLs and
   bucket custom domains disabled. Inventory any existing API keys or other writers.
3. Review other account R2 use: the monthly free allowances are shared.
4. Deploy `mei-cache-reader` with `CACHE` bound to `mei-cache`; retain
   `ENABLED=false` until validation. `workers.dev` provides the public entry point;
   no paid domain, KV, Durable Object, or other service is required.
5. Keep the S3 publisher credentials exclusively in the isolated trusted CI job.
   Do not give credentials to the public reader or candidate PR/build code.
6. Initialize the budget exactly once with `initialize-empty`, only for the
   dedicated empty bucket with no other writers or pending multipart uploads.
   Do not initialize or reset it automatically from CI.

## Publisher guards and remaining operational limits

- At most 10,000,000,000 bytes (10 GB, not 10 GiB) reserved, including a 64 KiB
  allowance for internal state. Reserve the entire candidate byte count before
  sending payloads; never refund overwrites, failed requests or deleted data.
  This is conservative: the publisher may stop before actual storage reaches
  10 GB. Other writers and manual uploads are outside this guarantee.
- Reserve at most 20,000 publication PUT operations per UTC day, including the
  reservation and completion writes. No automatic retries or multipart uploads.
- Publication stages all bytes locally without per-artifact public probes. The
  isolated writer deduplicates against an immutable SHA-256-pinned catalog of
  successful writes. It uploads only new artifacts, then the revision map.
  The first catalog publication uploads the current artifacts once. Never delete
  cataloged objects externally: the catalog assumes this exclusive writer.
- One budget GET and at most one private catalog GET are used per publication attempt. Rejected/contending attempts
  also incur control-plane operations; these are NOT a provider-enforced daily
  cap. Public verification remains behind the Free Worker. The earlier proposed
  10,000 direct Class B cap is not implemented; do not claim a total bill cap.
- Conditional R2 writes serialize reservations; a persistent active reservation
  blocks other writers even after a crash or a date change. GitHub concurrency
  also serializes main publication and explicit budget administration. Unknown outcomes fail closed.
- The workflow-pinned guard executes with credentials; candidate payloads remain
  inert. All artifacts finish before the full revision map is published.
- Automatic reclamation is not implemented. At capacity or after an interrupted
  publisher, inspect in-flight operations and actual data before a separately
  reviewed reconciliation. Do not blindly clear the lock or lower reservations.
- Preserve existing build success on an optional cache miss or budget stop;
  do not silently waive required Lean checks.

## Deployment inputs

Repository variables (only activate after verification):

- `MEI_R2_BUCKET_ENDPOINT`: `https://<account-id>.r2.cloudflarestorage.com/mei-cache`
- `LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC`: reader URL plus `/artifacts`
- `LAKE_CACHE_REVISION_ENDPOINT_PUBLIC`: reader URL plus `/revisions`
- `MEI_R2_GUARDS_READY`: `1`, after initialization and checks only

`LAKE_CACHE_KEY` is a bucket-scoped R2 Object Read & Write credential in the form
`access_key_id:secret_access_key`. Enter it directly into GitHub Actions secrets,
never a chat, commit, workflow literal or CLI argument. The reader needs no key.
Initialization requires the same secret passed as `LAKE_CACHE_KEY_RAW` and the
bucket endpoint as `MEI_R2_BUCKET_ENDPOINT` to:

```sh
python3 scripts/mei_r2_publish.py initialize-empty
```

Reader URL supplied by the user:
`https://mei-cache-reader.ymizuno-lean-cache.workers.dev`

## Acceptance before enabling

Verify anonymous real Lake restore, exact artifact bytes, GET and HEAD behavior,
unknown paths and write rejection, no direct public bucket access, and recovery
to a normal build when the reader returns 503. Exercise capacity overflow,
concurrent publishers, interrupted reservations, reruns, and exhausted operation
budgets using local mocks, not a load test against the live billed service.

The reader is designed to work with `lake cache get`; full compatibility has not
yet been tested against a deployed endpoint. Do not enable the old Releases
transport (`MEI_RELEASE_CACHE`) alongside this deployment.

## Official references checked 2026-10-28

- https://developers.cloudflare.com/workers/platform/limits/#daily-requests
- https://developers.cloudflare.com/r2/pricing/
- https://developers.cloudflare.com/r2/buckets/public-buckets/
- https://developers.cloudflare.com/r2/api/workers/workers-api-reference/
- https://developers.cloudflare.com/r2/buckets/object-lifecycles/

With one R2 read per public request, Workers Free admits at most 3.1 million
such reads in a 31-day month. This bound depends on the Free account plan and
the absence of bypass paths. It does not bound storage, writes, other consumers,
administrator changes or leaked credentials, and is not a contractual bill cap.

## Accounting for pre-existing objects

After stopping all external writers and confirming no in-flight uploads remain,
run the budget administration workflow with `operation=adopt-existing` and
`confirmation=mei-cache`. It locks the current budget, rejects multipart uploads,
checks up to 20 pages of objects, and adds their full size to existing reserved
bytes without refunds. This deliberately double-counts already reserved objects.
It never deletes payloads or clears a previously interrupted lock. Failure leaves
its own reservation locked for inspection. Only after confirmed success may
`MEI_R2_GUARDS_READY=1` re-enable main publication. Past unguarded operations are
not retroactively covered by the new operation budget.
