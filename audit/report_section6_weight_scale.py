from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
log = (root / 'audit/section6-weight-scale-audit.log').read_text(encoding='utf-8-sig')
assert not re.search(r'error(?:\(|:)', log)
expected = set()
for name in ['Section6WeightScaleConcentration.lean', 'Section6RandomWeightBridge.lean']:
    expected.update('Luce.Section6.' + n for n in re.findall(
        r'^theorem\s+([^\s{(]+)', (root / 'Luce' / name).read_text(encoding='utf-8'), re.M))
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
assert set(n for n, _ in reports) == expected
for name, deps in reports:
    actual = {re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in deps.split(',') if a.strip()}
    assert actual <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, actual)
text = '\n'.join([
    '# Proposition 6.5: weight-scale and random-time evidence', '',
    'Status: the full Proposition 6.5 and its closed contract check remain unproved.', '',
    f'This bounded audit checks exactly {len(expected)} theorems from the two named implementation modules.',
    'It does not assert a passing whole-project audit: that audit currently fails on unimported concurrent Lemma 6.6 declarations.', '',
    'The unchanged closed contract, fully elaborated theorem types, and actual transitive axiom output follow.', '',
    '```lean', log.strip(), '```', '',
    'No main-theorem or contract-check axiom output exists because those proofs remain absent.',
    'See section6-proposition65-audit.md for the full obligation ledger and actual command results.', ''])
(root / 'docs/section6-proposition65-weight-scale-evidence.md').write_text(text, encoding='utf-8')
print(f'Checked exactly {len(expected)} theorem types/axiom reports; permitted foundational axioms only.')
