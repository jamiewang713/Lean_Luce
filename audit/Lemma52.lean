import Luce.Section5Lemma52

/-!
Focused audit of the actual completed Lemma 5.2 declarations.
The proof audit and expanded-statement audit are separate.
Run with `lake env lean audit/Lemma52.lean` after `lake build`.
-/

-- A. Transitive axiom dependencies, checked by Lean's environment traversal.
#print axioms Luce.section5_bounded_marked_asymptotic
#print axioms Luce.section5_cyclic_local
#print axioms Luce.section5_lemma52
#print axioms Luce.ProfileLimit.weighted_bulk_cylinder_all
#print axioms Luce.exponentialRace_orderedNormalizedGaps
#print axioms Luce.markedRankCylinder_real_probability_eq_deletedGapProduct
#print axioms Luce.integrable_mixed_expMeasure_one
#print axioms Luce.integral_mixed_expMeasure_one
#print axioms Luce.markedRankCylinder_taylor_expectation
#print axioms Luce.ProfileLimit.deleted_suffix_rate_uniform_lower
#print axioms Luce.section5_uniform_marked_gap_coefficient
#print axioms Luce.section5_marked_coefficient_expectation
#print axioms Luce.ProfileLimit.integrable_cyclic_density
#print axioms Luce.cyclicProfileIntegral_eq_volume
#print axioms Luce.exists_cyclic_test_extension
#print axioms Luce.section5UnitWeights_assumptions

-- B. All implicit binders and typeclass arguments in the final types.
set_option pp.explicit true in
#check @Luce.section5_bounded_marked_asymptotic
set_option pp.explicit true in
#check @Luce.section5_cyclic_local
set_option pp.explicit true in
#check @Luce.section5_lemma52
set_option pp.explicit true in
#check @Luce.ProfileLimit.weighted_bulk_cylinder_all
set_option pp.explicit true in
#check @Luce.ProfileLimit.integrable_cyclic_density
set_option pp.explicit true in
#check @Luce.exists_cyclic_test_extension

-- Expand every custom object in the main types to inspect their meanings.
#print Luce.Weights
#print Luce.WeightArray
#print Luce.NormalizedWeights
#print Luce.ProfileLimit
#print Luce.ProfileL1Convergence
#print Luce.stepProfile
#print Luce.profileMeasure
#print Luce.exponentialRace
#print Luce.raceRank
#print Luce.cyclicRaceSum
#print Luce.cyclicBulkCube
#print Luce.cyclicProfileDensity
#print Luce.profileQuantile
#print Luce.profileF
#print Luce.profileH
#print Luce.profileD
#print Luce.rateKernel
#print Luce.survivalKernel
#print Luce.finiteCyclicDensity
#print Luce.ValidMarkedGapConfiguration
#print Luce.MarkedGapIndexData
