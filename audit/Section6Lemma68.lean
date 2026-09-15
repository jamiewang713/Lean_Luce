import Luce.Section6Lemma68Audit
import Lean.Util.CollectAxioms

set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false

#print Luce.Section6.Lemma68Contract.total
#print Luce.Section6.Lemma68Contract.spatial
#print Luce.Section6.idealTrace
#print Luce.Section6.idealRootTrace
#print Luce.Section6.idealTupleRoot
#print Luce.Section6.idealCoreLower
#print Luce.Section6.idealCoreUpper
#print Luce.Section6.idealSpatialTrace
#print Luce.Section6.localIdealKernel
#print Luce.Section6.cornerCoefficient
#print Luce.Section6.logDistinctTrace68_refined
#print Luce.Section6.idealTrace_refined68
#print Luce.Section6.idealRootTrace_left_sub68
#print Luce.Section6.idealRootTrace_right_sub68
#print Luce.Section6.lemma68_total
#print Luce.Section6.lemma68_spatial
#print Luce.Section6.lemma68
#print Luce.Section6.lemma68_contractCheck

example : Luce.Section6.Lemma68Contract.lemma68 := Luce.Section6.lemma68
example : Luce.Section6.Lemma68Contract.lemma68 := Luce.Section6.lemma68_contractCheck

-- Fail the audit if any transitive proof dependency uses a non-foundational axiom.
run_elab do
  let roots := #[``Luce.Section6.lemma68_total,
    ``Luce.Section6.lemma68_spatial,
    ``Luce.Section6.lemma68,
    ``Luce.Section6.lemma68_contractCheck,
    ``Luce.Section6.logDistinctTrace68_refined,
    ``Luce.Section6.relativeIdealTrace68_remainder,
    ``Luce.Section6.logGridTrace68_comparison,
    ``Luce.Section6.logDistinctTrace68_comparison,
    ``Luce.Section6.idealSpatialWindow68_eventually,
    ``Luce.Section6.TraceDensity68.continuous_root_trace]
  for name in roots do
    let axioms ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axioms}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Disallowed transitive axiom in {name}: {ax}"
  Lean.logInfo "LEMMA68_AXIOM_AUDIT_PASSED: only propext, Classical.choice and Quot.sound"
