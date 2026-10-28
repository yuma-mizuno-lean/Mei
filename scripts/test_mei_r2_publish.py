import datetime as dt
import json
from pathlib import Path
import tempfile
import unittest

from mei_r2_publish import A_LIMIT, LIMIT, STATE_ALLOWANCE, STATE_KEY, Stop, initial_state, load_plan, publish, reserve

TODAY = dt.datetime.now(dt.timezone.utc).date().isoformat()


class FakeR2:
    def __init__(self, fail_key=None, conflict=False):
        self.state = initial_state()
        self.etag = '0'
        self.calls = []
        self.fail_key, self.conflict = fail_key, conflict

    def request(self, method, key, data=None, headers=None):
        self.calls.append((method, key))
        if key == STATE_KEY:
            if method == 'GET':
                return 200, json.dumps(self.state).encode(), {'etag': self.etag}
            if self.conflict or headers['If-Match'] != self.etag:
                return 412, b'', {}
            self.state = json.loads(data)
            self.etag = str(int(self.etag) + 1)
            return 200, b'', {'etag': self.etag}
        if key == self.fail_key:
            raise Stop('unknown transport outcome')
        return 200, b'', {}


class BudgetTests(unittest.TestCase):
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
