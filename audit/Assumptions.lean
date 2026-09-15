import Luce.Assumptions

/-!
Inspect the manuscript assumption predicates without asserting that they hold.
Run after `lake build`: `lake env lean audit/Assumptions.lean`.
-/

#print Luce.WeightArray
#print Luce.NormalizedWeights
#print Luce.stepProfile
#print Luce.profileMeasure
#print Luce.ProfileL1Convergence
#print Luce.ProfileLimit
#print Luce.ProfileAssumption
#print Luce.EndpointAssumption

#print axioms Luce.WeightArray
#print axioms Luce.NormalizedWeights
#print axioms Luce.stepProfile
#print axioms Luce.profileMeasure
#print axioms Luce.ProfileL1Convergence
#print axioms Luce.ProfileLimit
#print axioms Luce.ProfileAssumption
#print axioms Luce.EndpointAssumption

#check MeasureTheory.eLpNorm_one_eq_lintegral_enorm
#print MeasureTheory.NullMeasurable
