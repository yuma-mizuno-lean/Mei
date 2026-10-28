// Anonymous, read-only Lake transport. No S3 credentials and no write route.
// COST INVARIANT: at most one R2 operation per incoming HTTP request.
const artifact = /^artifacts\/yuma-mizuno-lean\/Mei\/[0-9a-f]{16}\.art$/;
const revision = /^revisions\/yuma-mizuno-lean\/Mei\/tc\/leanprover--lean4---[0-9A-Za-z][0-9A-Za-z._+-]*\/[0-9a-f]{40}\.jsonl$/;

export default {
  async fetch(request, env) {
    const headers = { 'Cache-Control': 'no-store', 'X-Content-Type-Options': 'nosniff' };
    const reply = (status, message) => new Response(request.method === 'HEAD' ? null : message, { status, headers });
    // Default closed until account plan, direct access and publisher guards are verified.
    if (env.ENABLED !== 'true') return reply(503, 'Cache unavailable');
    if (request.method !== 'GET' && request.method !== 'HEAD') {
      return new Response('Read only', { status: 405, headers: { ...headers, Allow: 'GET, HEAD' } });
    }
    const url = new URL(request.url);
    const key = url.pathname.slice(1);
    if (url.search || !(artifact.test(key) || revision.test(key))) return reply(404, 'Not found');
    // Do not expand ranges, follow client URLs, list objects or expose internal state.
    if (request.headers.has('Range')) return reply(416, 'Range requests are not supported');
    try {
      const object = request.method === 'HEAD'
        ? await env.CACHE.head(key)
        : await env.CACHE.get(key);
      if (!object) return reply(404, 'Not found');
      const success = new Headers(headers);
      success.set('Content-Type', artifact.test(key)
        ? 'application/vnd.reservoir.artifact'
        : 'application/vnd.reservoir.outputs+json-lines');
      success.set('Content-Length', String(object.size));
      success.set('ETag', object.httpEtag);
      success.set('Cache-Control', 'public, max-age=3600');
      return new Response(request.method === 'HEAD' ? null : object.body, { headers: success });
    } catch {
      // Never retry inside the Worker: one invocation must not amplify R2 requests.
      return reply(503, 'Cache unavailable');
    }
  },
};
