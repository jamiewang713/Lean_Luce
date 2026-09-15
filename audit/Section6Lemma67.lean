import Luce.Section6Lemma67Totals
import Lean.Util.CollectAxioms

set_option pp.explicit true
set_option pp.universes true
set_option pp.proofs false

#check (Luce.Section6.lemma67 : Luce.Section6.Lemma67Contract.lemma67)
#print Luce.Section6.Lemma67Contract.active
#print Luce.Section6.Lemma67Contract.endpointEstimates
#print Luce.Section6.Lemma67Contract.regular
#print Luce.Section6.selectedRootCycleCount
#print Luce.Section6.logarithmicExcursionCount
#print Luce.Section6.offActiveLabels
#print Luce.Section6.lemma67
#check @Luce.Section6.lemma67_excursion_totals
#check @Luce.Section6.lemma67_regular_totals

#print axioms Luce.Section6.selected_root_count_le_vertices
#print axioms Luce.Section6.selected_root_expectation_of_rates
#print axioms Luce.Section6.PowerProfile.off_active_root_expectation
#print axioms Luce.Section6.cornerDistance_pos67
#print axioms Luce.Section6.cornerDistance_injective67
#print axioms Luce.Section6.log_distance_right_ratio
#print axioms Luce.Section6.log_distance_left_ratio
#print axioms Luce.Section6.harmonic_interval_sum67
#print axioms Luce.Section6.harmonic_real_subset67
#print axioms Luce.Section6.small_ratio_absorption67
#print axioms Luce.Section6.right_half_threshold67
#print axioms Luce.Section6.left_double_threshold67
#print axioms Luce.Section6.PowerProfile.right_root_log_probability
#print axioms Luce.Section6.PowerProfile.left_root_log_probability
#print axioms Luce.Section6.logarithmic_excursion_expectation_of_root_bound
#print axioms Luce.Section6.PowerProfile.active_log_expectation
#print axioms Luce.Section6.finite_uniform_cycle_constants
#print axioms Luce.Section6.endpointEstimates_mono67
#print axioms Luce.Section6.selected_root_singleton67
#print axioms Luce.Section6.PowerProfile.endpoint_estimates67
#print axioms Luce.Section6.lemma67_active
#print axioms Luce.Section6.lemma67_regular
#print axioms Luce.Section6.lemma67
#print axioms Luce.Section6.sum_cycle_expectations67
#print axioms Luce.Section6.lemma67_excursion_totals
#print axioms Luce.Section6.lemma67_regular_totals

-- A disallowed transitive axiom is a Lean error, not just a log entry.
run_elab do
  let roots := #[``Luce.Section6.lemma67,
    ``Luce.Section6.lemma67_excursion_totals,
    ``Luce.Section6.lemma67_regular_totals]
  for name in roots do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Disallowed transitive axiom in {name}: {ax}"
  Lean.logInfo "LEMMA67_AXIOM_AUDIT_PASSED: only propext, Classical.choice and Quot.sound"
