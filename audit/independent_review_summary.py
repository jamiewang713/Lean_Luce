"""Summarize fresh review evidence and detect source changes during review."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
inventory = json.loads((root/'audit/independent-review-source-inventory.json').read_text(encoding='utf-8'))
changed = []
for record in inventory['sources']:
    path = root/record['file']
    if not path.exists() or hashlib.sha256(path.read_bytes()).hexdigest() != record['sha256']:
        changed.append(record['file'])
current = {p.relative_to(root).as_posix() for folder in ['Luce','audit','proposals']
           for p in (root/folder).rglob('*.lean')} | {'Luce.lean'}
new = sorted(current-{record['file'] for record in inventory['sources']})
results_path = root/'audit/independent-review-ancillary/results.json'
results = json.loads(results_path.read_text(encoding='utf-8')) if results_path.exists() else []
failures = []
for record in results:
    if record['exit_code'] == 0:
        continue
    log = (root/record['log']).read_text(encoding='utf-8-sig', errors='replace')
    failures.append({**record,
        'diagnostics':re.findall(r'^.*\.lean:\d+:\d+: error(?:\([^)]*\))?:.*$',log,re.M),
        'unknown_constants':sorted(set(re.findall(r'Unknown constant `([^`]+)`',log)))})
ancillary = {p.relative_to(root).as_posix() for folder in ['audit','proposals']
             for p in (root/folder).glob('*.lean') if not p.name.startswith('IndependentReview')}
missing = sorted(ancillary-{record['file'] for record in results})
compiled = (root/'audit/independent-review-compiled.log').read_text(encoding='utf-8-sig', errors='replace')
summary = {
    'production_sources':inventory['counts']['Luce'],
    'changed_lean_sources_since_snapshot':changed,
    'changed_production_sources_since_snapshot':[p for p in changed if p == 'Luce.lean' or p.startswith('Luce/')],
    'new_lean_sources_since_snapshot':new,
    'current_ancillary_count':len(ancillary),
    'ancillary_completed':len(results),
    'ancillary_failures':failures,
    'ancillary_not_yet_checked':missing,
    'compiled_audit_summary':re.findall(r'^REVIEW_[^\n]+',compiled,re.M),
    'compiled_audit_passed':'REVIEW_PASSED:' in compiled,
    'final_build_passed':'Build completed successfully (4578 jobs).' in (root/'audit/independent-review-build-final.log').read_text(encoding='utf-8-sig',errors='replace'),
    'compiled_errors':re.findall(r'^.*\.lean:\d+:\d+: error(?:\([^)]*\))?:.*$',compiled,re.M),
    'manuscript_sha256':hashlib.sha256((root/'fixed_points_sampled_profile.tex').read_bytes()).hexdigest(),
    'final_audit_source_sha256':hashlib.sha256((root/'audit/IndependentReview.lean').read_bytes()).hexdigest(),
}
(root/'audit/independent-review-verification.json').write_text(json.dumps(summary,indent=2),encoding='utf-8')
main_names = {
    'section4_contractCheck', 'section5_contractCheck', 'cycleShell_contractCheck',
    'Luce.Section6.powerLaw65', 'Luce.Section6.spatial65', 'Luce.Section6.critical',
    'Luce.Section6.section65', 'Luce.Section6.lemma612', 'Luce.Section6.section6',
    'Luce.Section6.section6_contractCheck', 'Luce.Section7.proposition71',
}
statements = []
for m in re.finditer(r'^STATEMENT (\S+) : .*?(?=^STATEMENT |^REVIEW_|\Z)',compiled,re.M|re.S):
    if m.group(1) in main_names:
        statements.append(m.group())
(root/'audit/independent-review-main-statements.txt').write_text('\n'.join(statements),encoding='utf-8')
print(json.dumps(summary,indent=2))
