import Luce.Section5Lemma52
import Lean.Util.CollectAxioms

/-!
Read-only proof audit for Lemma 5.2. The final declarations are imported
from the built project. No proposition is introduced or proved here.
The environment walk below inspects existing checked declaration bodies;
it neither creates declarations nor supplies an evaluation oracle to a proof.
-/

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs false

#check @Luce.section5_bounded_marked_asymptotic
#check @Luce.section5_cyclic_local
#check @Luce.section5_lemma52
#check @Luce.ProfileLimit.integrable_cyclic_density
#check @Luce.cyclicProfileIntegral_eq_volume
#check @Luce.exists_cyclic_test_extension
#check @Luce.markedRankCylinder_taylor_expectation
#check @Luce.exponentialRace_raceNormalizedGaps_restrict_order
#check @Luce.integrable_selectedNormalizedGaps_mixed
#check @Luce.integral_selectedNormalizedGaps_mixed
#check @Luce.integral_selectedNormalizedGaps_taylorEnvelope
#check @Luce.ProfileLimit.weighted_bulk_cylinder_all

#print axioms Luce.section5_bounded_marked_asymptotic
#print axioms Luce.section5_cyclic_local
#print axioms Luce.section5_lemma52
#print axioms Luce.ProfileLimit.integrable_cyclic_density
#print axioms Luce.cyclicProfileIntegral_eq_volume
#print axioms Luce.exists_cyclic_test_extension
#print axioms Luce.markedRankCylinder_real_probability_eq_deletedGapProduct
#print axioms Luce.markedRankCylinder_taylor_expectation
#print axioms Luce.markedGap_taylor_expectation
#print axioms Luce.exponentialRace_identityNormalizedGaps_integral
#print axioms Luce.exponentialRace_raceNormalizedGaps_restrict_order
#print axioms Luce.exponentialRace_raceNormalizedGaps
#print axioms Luce.integrable_selectedNormalizedGaps_mixed
#print axioms Luce.integral_selectedNormalizedGaps_mixed
#print axioms Luce.integral_selectedNormalizedGaps_taylorEnvelope
#print axioms Luce.section5_marked_coefficient_expectation
#print axioms Luce.section5_sorted_marked_asymptotic
#print axioms Luce.bounded_marked_asymptotic_of_sorted
#print axioms Luce.ProfileLimit.cyclic_deterministic_limit
#print axioms Luce.ProfileLimit.tendsto_weighted_cyclic_array_sum
#print axioms Luce.ProfileLimit.cyclic_local_of_bounded_marked_asymptotic
#print axioms Luce.ProfileLimit.weighted_bulk_cylinder
#print axioms Luce.ProfileLimit.weighted_bulk_cylinder_all

/- Explicit proof terms at the final assembly boundary. -/
set_option pp.explicit false in
set_option pp.proofs true in
#print Luce.section5_bounded_marked_asymptotic
set_option pp.explicit false in
set_option pp.proofs true in
#print Luce.section5_cyclic_local
set_option pp.explicit false in
set_option pp.proofs true in
#print Luce.section5_lemma52

/- Walk actual checked types and bodies, independently of the source scan
and of the cached axiom lists printed above. Include constructors of
inductive types, following Lean's own axiom-collection convention. -/
set_option maxHeartbeats 0 in
run_elab do
  let env ← Lean.getEnv
  let roots : List Lean.Name := [``Luce.section5_bounded_marked_asymptotic,
    ``Luce.section5_cyclic_local, ``Luce.section5_lemma52]
  for root in roots do
    let some info := env.checked.get.find? root
      | throwError "Missing final declaration: {root}"
    unless info.isTheorem do
      throwError "Final declaration is not a theorem: {root}"
  let mut pending := roots
  let mut seen : Lean.NameSet := {}
  let mut localNames : Array Lean.Name := #[]
  let mut axiomNames : Lean.NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Missing transitive checked declaration: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial transitive declaration: {name}"
    if info.isAxiom then
      axiomNames := axiomNames.insert name
      unless [``propext, ``Classical.choice, ``Quot.sound].contains name do
        throwError "Additional transitive axiom: {name}"
    if name.toString.startsWith "Luce." || name.toString.startsWith "_private.Luce." then
      localNames := localNames.push name
    pending := info.type.getUsedConstants.toList ++ pending
    if let some value := info.value? true then
      pending := value.getUsedConstants.toList ++ pending
    if let .inductInfo value := info then
      pending := value.ctors ++ pending
  let localsSorted := localNames.qsort Lean.Name.lt
  Lean.logInfo m!"CHECKED_BODY_AUDIT: {seen.toArray.size} transitive declarations; {localsSorted.size} Luce declarations; no unsafe or partial declarations; no additional axioms."
  Lean.logInfo m!"CHECKED_BODY_AXIOMS: {axiomNames.toArray.qsort Lean.Name.lt}"
  for name in localsSorted do
    Lean.logInfo m!"CHECKED_LOCAL_DEPENDENCY: {name}"
