"""Record exact proof/build results and unchanged historical hash baselines."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
audit = root / 'audit'
manifest = json.loads((audit / 'section6-proposition610-manifest.json').read_text())
allowed = {'propext', 'Classical.choice', 'Quot.sound'}

def read(path):
    data = path.read_bytes()
    return data.decode('utf-16' if data.startswith((b'\xff\xfe', b'\xfe\xff')) else 'utf-8-sig')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inspect_log(path, names):
    text = read(path)
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        axioms = re.sub(r'\.\{[^}]*\}', '', axioms)
        found[name] = [a.strip() for a in axioms.split(',') if a.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        found[name] = []
    missing = sorted(set(names)-found.keys())
    extra = sorted(found.keys()-set(names))
    unexpected = {n: sorted(set(a)-allowed) for n, a in found.items() if set(a)-allowed}
    errors = [line for line in text.splitlines() if re.search(r'\berror(?:\([^)]*\))?:', line)]
    return {'expected_theorems': len(names), 'axiom_reports': len(found),
            'missing_reports': missing, 'extra_reports': extra,
            'unexpected_axioms': unexpected, 'lean_errors': errors,
            'passed': not (missing or extra or unexpected or errors)}

dedicated = inspect_log(audit / 'section6-proposition610-audit.log', manifest['theorems'])
current_source = read(audit / 'Section6Current.lean')
current_names = re.findall(r'^#print axioms (\S+)', current_source, re.M)
current = inspect_log(audit / 'section6-proposition610-current-audit.log', current_names)
supplement_names = re.findall(r'^#print axioms (\S+)',
    read(audit / 'Section6Proposition610NamespaceSupplement.lean'), re.M)
supplement = inspect_log(audit / 'section6-proposition610-namespace-supplement.log', supplement_names)
build_text = read(audit / 'section6-proposition610-build.log')
build_match = re.search(r'Build completed successfully \((\d+) jobs\)', build_text)
build = {'passed': bool(build_match) and not re.search(r'\berror(?:\([^)]*\))?:', build_text),
         'jobs': int(build_match.group(1)) if build_match else None}
snapshots = {}
for name in ['section6-proposition610-contract-freeze.json',
             'section6-lemma69-contract-freeze.json',
             'section6-proposition65-contract-freeze.json', 'section6-contract-freeze.json']:
    baseline = json.loads(read(audit / name))
    changed = {p: {'expected': h, 'actual': digest(root / p)}
               for p, h in baseline.items() if digest(root / p) != h}
    snapshots[name] = {'files': len(baseline), 'changed': changed, 'baseline_reset': False}
forbidden = {}
for rel in manifest['files']:
    text = read(root / rel)
    hits = re.findall(r'\bsorry\b|\badmit\b|^\s*axiom\b|\bunsafe\b|\bnative_decide\b', text, re.M)
    if hits:
        forbidden[rel] = hits
previous = json.loads(read(audit / 'section6-proposition65-validation.json'))
previous_changes = [p for p, h in previous['sha256'].items()
                    if p not in {'Luce/Section6.lean', 'fixed_points_sampled_profile.tex'}
                    and digest(root / p) != h]
frozen_non_manuscript_changes = {name: [p for p in result['changed']
    if p != 'fixed_points_sampled_profile.tex'] for name, result in snapshots.items()}
result = {
    'proposition610_complete': dedicated['passed'] and build['passed'] and not forbidden,
    'closed_targets': {'Luce.Section6.proposition610': 'Luce.Section6.Proposition610Contract.proposition610',
                       'Luce.Section6.proposition610_contractCheck': 'Luce.Section6.Proposition610Contract.proposition610'},
    'new_modules': len(manifest['files']), 'new_theorems': len(manifest['theorems']),
    'full_build': build, 'dedicated_audit': dedicated, 'allowed_axioms': sorted(allowed),
    'forbidden_source_constructs': forbidden, 'snapshots': snapshots,
    'section6_audit_snapshot': current, 'prior_proposition65_component_changes': previous_changes,
    'namespace_supplement': supplement,
    'broader_audit_issue': 'The unchanged generator omits TraceDensity68 from five existing declaration names. Its failed run is retained; a separate supplement checks their actual qualified names.',
    'frozen_non_manuscript_changes': frozen_non_manuscript_changes,
    'snapshot_note': 'The manuscript changed outside this task after the Proposition 6.10 snapshot. No manuscript or historical baseline was edited by this proof task. Differences are retained as failures, not reset.',
    'sha256': {p: digest(root / p) for p in manifest['files']},
}
(audit / 'section6-proposition610-validation.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(json.dumps({k: result[k] for k in ['proposition610_complete', 'new_modules', 'new_theorems',
                                      'full_build', 'dedicated_audit', 'prior_proposition65_component_changes']}, indent=2))
print(f"Whole Section 6 audit: {current['axiom_reports']}/{current['expected_theorems']}, passed={current['passed']}")
print('Frozen mismatches:', {n: list(s['changed']) for n, s in snapshots.items()})
if (not result['proposition610_complete'] or previous_changes or not supplement['passed']
        or any(frozen_non_manuscript_changes.values())):
    raise SystemExit(1)
