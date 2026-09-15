import Luce.Section4

/-! Proof and statement audit for the complete Section 4 dependency chain.
Run with `lake env lean audit/Section4.lean` after `lake build`.
-/

set_option pp.explicit true in
#check @Luce.section4_main_poisson
set_option pp.explicit true in
#check @Luce.section4_main_poisson_general
set_option pp.explicit true in
#check @Luce.section4_full_poisson
set_option pp.explicit true in
#check @Luce.section4_full_poisson_general
set_option pp.explicit true in
#check @Luce.section4_count_poisson
set_option pp.explicit true in
#check @Luce.section4_count_poisson_general
set_option pp.explicit true in
#check @Luce.section4_tail_expectation_bound_of_endpoint_witness

-- Readable versions accompany the fully explicit kernel-facing types above.
#check @Luce.section4_main_poisson
#check @Luce.section4_main_poisson_general
#check @Luce.section4_tail_expectation_bound_of_endpoint_witness

set_option pp.explicit true in
#check @Luce.section4_endpoint_bound
set_option pp.explicit true in
#check @Luce.section4_tail_expectation_bound
set_option pp.explicit true in
#check @Luce.section4_point_measure_tail_tightness
set_option pp.explicit true in
#check @Luce.section4_intensity_test_bound
set_option pp.explicit true in
#check @Luce.section4_full_intensity_finite
set_option pp.explicit true in
#check @Luce.section4_profileDiagonal_integrable
set_option pp.explicit true in
#check @Luce.section4_intensity_tail_tendsto

#print Luce.NormalizedWeights
#print Luce.ProfileLimit
#print Luce.EndpointAssumption
#print Luce.Weights
#print Luce.profileDiagonal
#print Luce.interiorDensityMeasure
#print Luce.interiorFixedPoints
#print Luce.tailFixedPointCount
#print Luce.WeightArray
#print Luce.Weights.mass
#print Luce.stepProfile
#print Luce.ProfileL1Convergence
#print Luce.profileMeasure
#print Luce.profileQuantile
#print Luce.profileF
#print Luce.profileH
#print Luce.profileD
#print Luce.rateKernel
#print Luce.survivalKernel
#print Luce.FinitePointMeasure
#print Luce.fullIntensity
#print Luce.fixedPoints
#print Luce.fixedPointCount
#print Luce.fixedPointCountLaw
#print Luce.probabilityTotalVariation
#print Luce.poissonProbabilityMeasure
#print Luce.finitePoissonLaw
#check @Luce.fullIntensity_projection_recovery
#check @Luce.fixedPoints_realMeasure
#check @Luce.fixedPointCount_eq_card

#print axioms Luce.rank_integral
#print axioms Luce.two_candidate_sum_bound
#print axioms Luce.integral_sum_clockSurvivalIndicator
#print axioms Luce.tailFixedPointCount_expectation_eq
#print axioms Luce.section4_endpoint_bound
#print axioms Luce.section4_tail_expectation_bound
#print axioms Luce.ConvergesInProbability.le_limsup_integral
#print axioms Luce.fixedPoints_tail_count
#print axioms Luce.section4_point_measure_tail_tightness
#print axioms Luce.FiniteAdaptedBernoulli.integral_predictable_eq_observed
#print axioms Luce.section4_interior_test_expectation_lower
#print axioms Luce.section4_intensity_test_bound
#print axioms Luce.section4_interior_intensity_bounded
#print axioms Luce.section4_full_intensity_finite
#print axioms Luce.section4_profileDiagonal_integrable
#print axioms Luce.section4_intensity_tail_tendsto
#print axioms Luce.section3_interior_poisson
#print axioms Luce.finitePoissonLaw_count_joint
#print axioms Luce.endpoint_window_le_row_of_size_condition
#print axioms Luce.section4_tail_expectation_bound_of_endpoint_witness
#print axioms Luce.fullIntensity_projection_recovery
#print axioms Luce.fullIntensity_mass
#print axioms Luce.tendsto_laplace_finitePoissonLaw_interior_full
#print axioms Luce.section4_laplace_cutoff_error
#print axioms Luce.pointMeasure_tightness_of_laplace
#print axioms Luce.section4_full_laplace
#print axioms Luce.section4_full_poisson
#print axioms Luce.section4_full_poisson_general
#print axioms Luce.finitePoissonLaw_count_univ
#print axioms Luce.pointMeasure_random_count_singleton_poisson_tendsto
#print axioms Luce.tendsto_probabilityTotalVariation_of_singletons
#print axioms Luce.tendsto_probabilityTotalVariation_of_integrals
#print axioms Luce.fixedPointCount_eq_card
#print axioms Luce.fullIntensity_mass_eq_toNNReal_integral
#print axioms Luce.section4_count_poisson
#print axioms Luce.section4_count_poisson_general
#print axioms Luce.fixedPoints_realMeasure
#print axioms Luce.section4_lambda_nonneg
#print axioms Luce.section4_main_poisson
#print axioms Luce.section4_main_poisson_general
