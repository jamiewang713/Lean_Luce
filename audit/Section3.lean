import Luce.Section3

/-!
Section 3 proof and statement audit. Run after `lake build`:
  lake env lean audit/Section3.lean
The axiom commands inspect transitive kernel dependencies; the type and
definition commands separately expose the mathematical statement.
-/

-- A. Main statements and substantive proof/representation dependencies.
#print axioms Luce.section3_uniform_race_general
#print axioms Luce.section3_order_statistics_general
#print axioms Luce.section3_uniform_remaining_weight_general
#print axioms Luce.section3_weighted_compensator_on_interval
#print axioms Luce.section3_max_probability_general
#print axioms Luce.section3_weighted_compensator_luce
#print axioms Luce.section3_max_probability_luce
#print axioms Luce.section3_interior_poisson
#print axioms Luce.section3_interior_poisson_general
#print axioms Luce.finitePoissonLaw_count_joint
#print axioms Luce.ProfileLimit.max_weight_div_tendsto_zero
#print axioms Luce.ProfileLimit.integral_eq_one
#print axioms Luce.section3_survival_replacement
#print axioms Luce.section3_survival_fluctuation
#print axioms Luce.ProfileLimit.deterministic_expectation_limit
#print axioms Luce.denominator_replacement_converges
#print axioms Luce.integrable_interior_density
#print axioms Luce.exponentialRace_order_probability
#print axioms Luce.raceDraw_mass
#print axioms Luce.luce_map_eq_raceDraw
#print axioms Luce.raceInteriorBernoulli_probability
#print axioms Luce.interiorFixedPoints_toFiniteMeasure
#print axioms Luce.interiorFixedPoints_realMeasure
#print axioms Luce.interiorDensityMeasure_eq_closed
#print axioms Luce.interior_integral_eq_closed
#print axioms Luce.interiorIntensity_projection_recovery
#print axioms Luce.integral_interiorIntensity
#print axioms Luce.predictable_poisson_of_integrals
#print axioms Luce.natCountLaw_eq_of_laplace
#print axioms Luce.FinitePointMeasure.count_coe_eq
#print axioms Luce.section3UnitWeights_normalized
#print axioms Luce.section3UnitWeights_profileLimit

-- B. Full elaborated types, including implicit arguments and instances.
set_option pp.explicit true in
#check @Luce.section3_uniform_race_general
set_option pp.explicit true in
#check @Luce.section3_order_statistics_general
set_option pp.explicit true in
#check @Luce.section3_uniform_remaining_weight_general
set_option pp.explicit true in
#check @Luce.section3_weighted_compensator_on_interval
set_option pp.explicit true in
#check @Luce.section3_max_probability_general
set_option pp.explicit true in
#check @Luce.section3_weighted_compensator_luce
set_option pp.explicit true in
#check @Luce.section3_max_probability_luce
set_option pp.explicit true in
#check @Luce.section3_interior_poisson
set_option pp.explicit true in
#check @Luce.section3_interior_poisson_general
set_option pp.explicit true in
#check @Luce.finitePoissonLaw_count_joint
set_option pp.explicit true in
#check @Luce.interiorIntensity_projection_recovery
set_option pp.explicit true in
#check @Luce.exponentialRace_order_probability
set_option pp.explicit true in
#check @Luce.raceInteriorBernoulli_probability

-- Expand every custom object used in the mathematical contract.
#print Luce.Weights
#print Luce.WeightArray
#print Luce.NormalizedWeights
#print Luce.ProfileLimit
#print Luce.ProfileL1Convergence
#print Luce.stepProfile
#print Luce.profileMeasure
#print Luce.profileF
#print Luce.profileH
#print Luce.profileD
#print Luce.rateKernel
#print Luce.survivalKernel
#print Luce.profileQuantile
#print Luce.profileDiagonal
#print Luce.empiricalArrival
#print Luce.empiricalRemainingGe
#print Luce.orderTime
#print Luce.arrivalTime
#print Luce.drawPermutation
#print Luce.rankPermutation
#print Luce.clockRank
#print Luce.raceDraw
#print Luce.Weights.mass
#print Luce.Weights.total
#print Luce.Weights.choice
#print Luce.remaining
#print Luce.predictableChance
#print Luce.interiorCompensatorSum
#print Luce.luceInteriorCompensatorSum
#print Luce.intervalTestExtension
#print Luce.ConvergesInProbability
#print Luce.section3Location
#print Luce.interiorFixedPoints
#print Luce.observedPointMeasure
#print Luce.interiorDensityMeasure
#print Luce.interiorIntensity
#print Luce.FinitePointMeasure
#print Luce.pointMeasureOfFin
#print Luce.FinitePointMeasure.count
#print Luce.finitePoissonLaw
#print Luce.iidPointLaw
#print Luce.poissonMixture
#print Luce.FiniteAdaptedBernoulli
#print Luce.raceInteriorBernoulli
#print Luce.FiniteAdaptedBernoulli.probability
#print Luce.BernoulliProcess.rowMaximum
