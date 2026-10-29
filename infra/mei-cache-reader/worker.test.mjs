import test from 'node:test';
import assert from 'node:assert/strict';
import worker from './worker.mjs';

const path = '/artifacts/yuma-mizuno-lean/Mei/0123456789abcdef.art';
const map = '/revisions/yuma-mizuno-lean/Mei/tc/leanprover--lean4---v4.36.0-rc1/' + 'a'.repeat(40) + '.jsonl';
function bucket({ missing = false, broken = false } = {}) {
  const calls = [];
  const read = async (method, key) => {
    calls.push([method, key]);
    if (broken) throw new Error('backend unavailable');
    if (missing) return null;
    return { size: 4, httpEtag: '"etag"', body: new Blob(['test']).stream() };
  };
  return { calls, get: key => read('get', key), head: key => read('head', key) };
}
async function run(pathname, method = 'GET', options = {}) {
  const CACHE = bucket(options);
  const result = await worker.fetch(new Request('https://cache.example' + pathname, {
    method, headers: options.headers,
  }), { CACHE, ENABLED: options.enabled ?? 'true' });
  return { result, calls: CACHE.calls };
}
test('anonymous artifact and revision reads preserve bytes with exactly one operation', async () => {
  for (const pathname of [path, map]) {
    const { result, calls } = await run(pathname);
    assert.equal(result.status, 200);
    assert.equal(await result.text(), 'test');
    assert.deepEqual(calls, [['get', pathname.slice(1)]]);
  }
});
test('HEAD does not fetch the body', async () => {
  const { result, calls } = await run(path, 'HEAD');
  assert.equal(result.status, 200);
  assert.equal(await result.text(), '');
  assert.deepEqual(calls, [['head', path.slice(1)]]);
});
test('unrecognized paths, writes, queries and ranges never touch R2', async () => {
  for (const [pathname, method, options] of [
    [path, 'PUT'], [path, 'DELETE'], ['/'], ['/budget.json'],
    [path.replace('Mei', 'Other')], [path + '?random=1'],
    [path, 'GET', { headers: { Range: 'bytes=0-1,2-3' } }],
  ]) {
    const { result, calls } = await run(pathname, method, options);
    assert.ok(result.status >= 400);
    assert.deepEqual(calls, []);
  }
});
test('backend errors and missing objects do not retry', async () => {
  for (const options of [{ missing: true }, { broken: true }]) {
    const { result, calls } = await run(path, 'GET', options);
    assert.ok(result.status >= 400);
    assert.equal(calls.length, 1);
  }
});
test('disabled deployment cannot read R2', async () => {
  const { result, calls } = await run(path, 'GET', { enabled: 'false' });
  assert.equal(result.status, 503);
  assert.deepEqual(calls, []);
});
