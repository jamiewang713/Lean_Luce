"""Extract completion evidence without altering any validator or frozen baseline."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
log = (root / 'audit/section6-current-audit.log').read_text(encoding='utf-8-sig')
reports = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S))
expected = set()
for path in (root / 'Luce').glob('Section6*.lean'):
    expected.update('Luce.Section6.' + n for n in re.findall(
        r'^theorem\s+([^\s{(]+)', path.read_text(encoding='utf-8'), re.M))
assert set(reports) == expected
for name, deps in reports.items():
    actual = {re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in deps.split(',') if a.strip()}
    assert actual <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, actual)
freeze = json.loads((root / 'audit/section6-lemma64-contract-freeze.json').read_text())
assert all(hashlib.sha256((root / p).read_bytes()).hexdigest() == h for p, h in freeze.items())
build = (root / 'audit/section6-progress-build.log').read_text(encoding='utf-8-sig')
assert 'Build completed successfully (4266 jobs).' in build

out = ['# Lemma 6.4: completion evidence', '',
    'The full frozen Lemma 6.4 proposition is proved, including its matrix and literal cycle-count components. '
    'This is not a claim about later Section 6 lemmas or any main CLT.', '',
    '## Statement and assumption audit', '',
    'The source is fixed_points_sampled_profile.tex, Assumption ass:simple-power-profile (line 385), '
    'Lemma lem:sp-domination (line 2141), and its stated fixed-index estimates. '
    'The complete hypothesis/type audit is in docs/section6-lemma64-contract.md. '
    'The exact closed contract below was frozen before the combined proof. '
    'All 45 files in its project import/source/configuration snapshot remain unchanged.', '',
    'REMOVED mathematical inputs: none. ADDED mathematical inputs: none. '
    'OTHER mathematical input or conclusion changes: none. '
    'The old uniform-endpoint-to-shell replacement belongs to Sections 4 and 5; '
    'neither endpoint predicate nor normalization is an assumption of this Section 6 lemma.', '',
    'The only model antecedents are the original positive continuous sampled power profile and exact sampling. '
    'Constants, cutoffs, matrix, and positive exponents are constructed outputs. '
    'Both sampling grids are covered; midpoint specializes to the manuscript. '
    'Fin n is the zero-based representation of labels 1,...,n; right depth is n-i.val; '
    'cycle length is k+1. Probability, rank, cycle, maximum-root, and discarded-count meanings are unchanged.', '',
    '## Actual fully elaborated theorem types and axiom output', '']
for short in ['lemma64', 'lemma64_contractCheck', 'lemma64_matrix', 'lemma64_cycles']:
    name = 'Luce.Section6.' + short
    match = re.search(r'^theorem ' + re.escape(name) + r' :[\s\S]*?\n' +
        re.escape("'" + name + "' depends on axioms:") + r' \[[\s\S]*?\]', log, re.M)
    assert match, name
    out += ['```lean', match.group(0), '```', '']
out += ['These are closed types: no additional explicit, implicit, universe, or instance parameters occur. '
    'The audit used pp.explicit, pp.universes and pp.fullNames. '
    'All ' + str(len(expected)) + ' Section 6 declarations have transitive axiom reports containing only '
    'propext, Classical.choice and Quot.sound. No sorryAx or project axiom occurs.', '',
    '## Complete closed contract (unchanged source)', '', '```lean',
    (root / 'Luce/Section6Lemma64Contract.lean').read_text(encoding='utf-8'), '```', '',
    '## Fully elaborated closed contract definitions (actual Lean output)', '', '```lean',
    log[log.index('def Luce.Section6.Lemma64Contract.matrix :'):log.index('def Luce.Section6.intervalDiscardedCycleCount')],
    '```', '',
    '## Proof and obligation discharge', '',
    'The complete current ledger is docs/section6-obligation-ledger.md. '
    'Section6Lemma64Matrix constructs M from the actual insertion domination matrix at order r+1. '
    'It derives the left envelope, right cutoff and endpoint target/column cutoff, intersects those cutoffs, '
    'then obtains the right decay and interior estimates at the FINAL cutoff. '
    'It constructs the common weighted exponent and chooses C=1+L+R+T+W+B+I+J. '
    'Every helper premise is discharged by the profile, sampling, or already proved numeric positivity. '
    'Section6Lemma64Cycles constructs its count bounds from exact count/indicator identities and the '
    'proved endpoint and interior expectation estimates. No Lemma 6.4 estimate remains an assumed input.', '',
    '## Commands and actual results', '',
    '- Individual Lean compilation of Section6ActiveEnvelopes and Section6Lemma64Matrix: exit 0 after fixing elaboration errors; no statement edits.',
    '- lake build Luce.Section6Lemma64Audit: exit 0, 4064 jobs (audit/section6-lemma64-contract-build.log).',
    '- lake build: exit 0, 4266 jobs (audit/section6-progress-build.log).',
    '- python audit/generate_section6_current_audit.py: 650 source declarations.',
    '- lake env lean audit/Section6Current.lean: exit 0 (audit/section6-current-audit.log).',
    '- python audit/freeze_section6_lemma64_contract.py: 45 frozen files, changed=[].',
    '- python audit/validate_section6_progress.py: FAILED at line 21 on the older manuscript hash, after passing declaration-set and axiom-whitelist checks.', '',
    '## Preserved historical limitation', '',
    'The original 13-file Section 6 freeze still differs at fixed_points_sampled_profile.tex. '
    'It was not reset or repaired; its old manuscript contents are unavailable. '
    'The later independent 45-file Lemma 6.4 freeze, created before the combined proof, passes. '
    'This report does not claim the old global validator passed, nor that the full historical manuscript is unchanged. '
    'The current source assumption and complete Lemma 6.4 statement were reread and compared against the frozen contract. '
    'Later density/trace/collision arguments and main CLTs remain outside this completion claim.', '']
(root / 'docs/section6-lemma64-completion.md').write_text('\n'.join(out), encoding='utf-8')
print(json.dumps({'theorems_audited': len(expected), 'frozen_files': len(freeze),
    'lemma64_proved': True, 'old_global_validator_passed': False}))
