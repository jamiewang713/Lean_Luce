"""Extract checked evidence; this does not alter either frozen baseline."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
log = (root / 'audit/section6-current-audit.log').read_text(encoding='utf-8-sig')
names = [
    'deleted_order_normalized_integral',
    'deleted_order_kernel_product_integral',
    'deleted_kernel_product_order_sum',
    'endpoint_block_terminal_buffer',
    'sorted_gap_nonfinal_of_terminal_buffer',
    'separated_cylinder_order_sum',
    'normalized_insertion_product_bounds',
    'normalized_insertion_product_integrable',
    'normalized_skeleton_integral',
    'later_selected_rate_reindex',
    'marked_normalized_skeleton_integral',
    'separated_cylinder_skeleton_formula',
    'ordered_remaining_rate_antitone',
    'skeleton_displacement_bound',
    'bernoulli_sum_exp_integrable',
    'bernoulli_relative_upper_tail',
    'bernoulli_relative_lower_tail',
    'deleted_arrival_relative_tails',
    'deleted_survivor_relative_tails',
    'deleted_arrivals_le_beforeCount_of_lt',
    'deleted_gapStart_gt_imp_arrivals_le',
    'deleted_gap_start_relative_early_arrival',
    'deleted_gap_start_relative_late_arrival',
    'deleted_arrivals_add_survivors',
    'deleted_gap_start_relative_early_survivor',
    'deleted_gap_start_relative_late_survivor',
    'scaled_deletion_error',
    'PowerProfile.left_deleted_quantile_separation',
    'PowerProfile.right_deleted_quantile_separation',
    'relative_mean_separation',
    'PowerProfile.left_gap_quantile_window',
    'PowerProfile.right_gap_quantile_window',
    'sorted_gap_left_displacement',
    'sorted_gap_right_displacement',
    'survival_indicator_memLp_two',
    'survival_indicator_variance_le_mean',
    'deleted_remaining_weight_variance',
    'deleted_remaining_weight_mean',
    'deleted_remaining_weight_chebyshev',
    'deletedD_le_populationD',
    'deleted_weight_scaled_chebyshev',
    'PowerProfile.right_weight_quantile_concentration',
    'PowerProfile.left_weight_quantile_concentration',
    'deleted_surviving_weight_antitone',
    'raceGapRate_eq_surviving_weight',
    'deleted_gap_rate_eq_surviving_weight',
    'deleted_weight_random_time_bound',
    'deleted_gap_rate_eq_surviving_weight_ae',
]
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
expected = set()
for p in (root / 'Luce').glob('Section6*.lean'):
    expected.update('Luce.Section6.' + n for n in
                    re.findall(r'^theorem\s+([^\s{(]+)', p.read_text(encoding='utf-8'), re.M))
assert set(n for n, _ in reports) == expected
for n, deps in reports:
    actual = {re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in deps.split(',') if a.strip()}
    assert actual <= {'propext', 'Classical.choice', 'Quot.sound'}, (n, actual)
out = ['# Proposition 6.5 order-transfer proof evidence', '',
       'Status: Proposition65Contract.localLaw and proposition65_contractCheck remain UNPROVED.',
       'These are supporting theorems, not a completed Proposition 6.5.', '',
       f'Full current source/type/axiom audit: {len(expected)} declarations; permitted axioms only.', '',
       '## Actual elaborated theorem types and transitive axiom output', '']
for name in names:
    full = 'Luce.Section6.' + name
    header = re.search(r'theorem ' + re.escape(full) + r'(?:\.\{[^}]*\})?\s', log)
    assert header, full
    start = header.start()
    axiom = re.search(r"'" + re.escape(full) + r"' depends on axioms: \[[^\]]*\]", log[start:], re.S)
    assert axiom
    out.extend(['### ' + name, '', '```lean', log[start:start + axiom.end()].strip(), '```', ''])
out.extend(['## Exact closed target (unchanged; no proof claimed)', '', '```lean',
            (root / 'Luce/Section6Proposition65Contract.lean').read_text(encoding='utf-8').strip(), '```', '',
            'There is no main-theorem or contract-check axiom output: neither theorem has been declared.',
            'The obligation ledger and command results are in section6-proposition65-audit.md.', ''])
(root / 'docs/section6-proposition65-transfer-evidence.md').write_text('\n'.join(out), encoding='utf-8')
print(f'Checked {len(expected)} axiom reports; extracted {len(names)} full supporting theorem types.')
