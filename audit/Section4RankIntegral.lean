import Luce.Section4ApprovedRankIntegral

/-!
Reproducible inspection of the pilot approved on 2026-09-10.
Run after `lake build`:
  lake env lean audit/Section4RankIntegral.lean
This file declares no axioms, definitions, instances, or theorems.
-/

#print Luce.rankOf
#print Luce.otherSurvivors
#print Luce.rank_integral
#print Luce.rank_integrand_integrable

#print axioms Luce.rankOf
#print axioms Luce.otherSurvivors
#print axioms Luce.measurable_rankOf
#print axioms Luce.measurable_otherSurvivors
#print axioms Luce.measurable_survivorProbability
#print axioms Luce.rank_integrand_integrable
#print axioms Luce.rank_integral

#check ProbabilityTheory.HasLaw
#check ProbabilityTheory.HasLaw.measureReal_eq
#check ProbabilityTheory.iIndepFun.hasLaw_pi
#check measurable_measure_prodMk_left
#check MeasureTheory.measureReal_le_one
#check integrableOn_exp_mul_Ioi

#print axioms ProbabilityTheory.iIndepFun.hasLaw_pi
#print axioms ProbabilityTheory.HasLaw.measureReal_eq
#print axioms integrableOn_exp_mul_Ioi
