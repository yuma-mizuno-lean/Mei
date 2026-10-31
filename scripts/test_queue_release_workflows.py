"""Check the caller wiring; admission policy remains in the pinned shared engine."""
from pathlib import Path
import ast
import datetime
import hashlib
import itertools
import os
import shlex
import tomllib
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[1]


def workflow(name):
    # BaseLoader keeps GitHub's `on` key a string rather than YAML 1.1's True.
    return yaml.load((ROOT / '.github/workflows' / name).read_text(), Loader=yaml.BaseLoader)


class QueueReleaseWorkflows(unittest.TestCase):
    def test_failed_admission_wakes_only_existing_bounded_sweep(self):
        job = workflow('auto-merge.yml')['jobs']['reconcile-after-failed-admission']
        self.assertEqual(job['needs'], 'merge')
        self.assertEqual(job['if'], "${{ always() && needs.merge.result == 'failure' }}")
        self.assertEqual(job['permissions'], {'contents': 'read', 'actions': 'write'})
        self.assertEqual(len(job['steps']), 1)
        step = job['steps'][0]
        self.assertEqual(step['env']['GH_TOKEN'], '${{ github.token }}')
        self.assertEqual(step['run'], 'gh workflow run merge-sweep.yml --repo "$REPO" --ref main -f dry-run=false -f full-scan=true')

    def test_release_runs_trusted_main_with_existing_tools_pin(self):
        release = workflow('queue-release.yml')
        self.assertEqual(release['on']['pull_request_target'],
                         {'branches': ['main'], 'types': ['closed', 'dequeued']})
        steps = release['jobs']['release']['steps']
        self.assertEqual(steps[0]['uses'], 'actions/checkout@11d5960a326750d5838078e36cf38b85af677262')
        self.assertEqual(steps[0]['with']['ref'], 'main')
        self.assertEqual(steps[0]['with']['persist-credentials'], 'false')
        tools = tomllib.loads((ROOT / 'tauceti.toml').read_text())['tools']['tools']
        setup = steps[1]
        self.assertEqual(setup['uses'], f"{tools['repo']}/.github/actions/setup@{tools['ref']}")
        self.assertEqual(setup['with']['tools-ref'], tools['ref'])
        self.assertEqual(setup['with']['tools-repository'], tools['repo'])
        self.assertEqual(steps[-1]['if'], "steps.release.outputs.sweep == 'true'")
        self.assertNotIn('secrets.', str(release))

    def test_displaced_unlabelled_pr_is_reconsidered_by_both_dispatches(self):
        # Execute only the pinned engine's pure selector, never its API/mutation code:
        # https://github.com/TauCetiProject/TauCetiReview/blob/3999677031829254b4cbb27e9156c33672c61d0d/runner/sweep.py#L575
        engine = Path(os.environ.get('TAUCETI_REVIEW_ROOT', ROOT / '.tauceti-review'))
        tree = ast.parse((engine / 'runner/sweep.py').read_text())
        selected = [node for node in tree.body
                    if (isinstance(node, ast.FunctionDef) and node.name in {'candidates', 'has_keep_label'})
                    or (isinstance(node, ast.Assign) and any(isinstance(t, ast.Name)
                        and t.id in {'KEEP_LABELS', 'NEEDS_REBASE_LABEL'} for t in node.targets))]
        namespace = dict(datetime=datetime, hashlib=hashlib, itertools=itertools, FOCUSED=True)
        exec(compile(ast.Module(body=selected, type_ignores=[]), 'pinned-candidate-selector', 'exec'), namespace)
        prs = [{'number': 608, 'isDraft': False, 'labels': []},
               {'number': 609, 'isDraft': False, 'labels': [{'name': 'hold'}]},
               {'number': 610, 'isDraft': True, 'labels': []}]
        self.assertEqual(namespace['candidates'](prs, set(), set()), [])
        dispatches = [workflow('auto-merge.yml')['jobs']['reconcile-after-failed-admission']['steps'][0]['run'],
                      workflow('queue-release.yml')['jobs']['release']['steps'][-1]['run']]
        for dispatch in dispatches:
            with self.subTest(dispatch=dispatch):
                inputs = dict(word.split('=', 1) for word in shlex.split(dispatch) if '=' in word)
                namespace['FOCUSED'] = inputs.get('full-scan', 'false') != 'true'
                self.assertEqual([p['number'] for p in namespace['candidates'](prs, set(), set())], [608])

if __name__ == '__main__':
    unittest.main()
