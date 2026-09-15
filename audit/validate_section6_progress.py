from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
log = (root / 'audit/section6-current-audit.log').read_text(encoding='utf-8-sig')
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
expected = set()
for p in (root / 'Luce').glob('Section6*.lean'):
    for name in re.findall(r'^theorem\s+([^\s{(]+)', p.read_text(encoding='utf-8'), re.M):
        expected.add('Luce.Section6.' + name)
assert {name for name, _ in reports} == expected
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, deps in reports:
    actual = {re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in deps.split(',') if a.strip()}
    assert actual <= allowed, (name, actual)
freeze = json.loads((root / 'audit/section6-contract-freeze.json').read_text())
changed = [p for p, h in freeze.items()
           if hashlib.sha256((root / p).read_bytes()).hexdigest() != h]
assert not changed, changed
build = (root / 'audit/section6-progress-build.log').read_text(encoding='utf-8-sig')
build_match = re.search(r'Build completed successfully \((\d+) jobs\)\.', build)
assert build_match, 'No successful build completion in the current build log'
result = {'proved_source_theorems': len(expected), 'axiom_reports': len(reports),
          'allowed_axioms_only': True, 'frozen_files': len(freeze), 'changed': changed,
          'build_jobs': int(build_match.group(1)), 'main_CLTs_complete': False}
(root / 'audit/section6-progress-validation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
