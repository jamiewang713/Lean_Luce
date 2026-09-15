import Luce.Section5

#print axioms Luce.section5_proposition54
#print axioms Luce.ProfileLimit.low_rate_cycles_vanish
set_option pp.explicit true in
#check @Luce.section5_proposition54

/-!
Two separate inspections of the delivered Section 5 progress.
Run `lake build` and `lake env lean audit/Section5.lean`.
No final Poisson-limit theorem is declared or claimed by this entry point.
-/

-- A. Transitive proof/axiom inspection of the kernel-checked declarations.
#print axioms Luce.ProfileLimit.moderate_reservoir
#print axioms Luce.section5_bounded_marked_asymptotic
#print axioms Luce.section5_cyclic_local
#print axioms Luce.section5_lemma52
#print axioms Luce.ProfileLimit.weighted_bulk_cylinder_all
set_option pp.explicit true in
#check @Luce.section5_bounded_marked_asymptotic
set_option pp.explicit true in
#check @Luce.section5_cyclic_local
set_option pp.explicit true in
#check @Luce.section5_lemma52
#print axioms Luce.ProfileLimit.moderate_reservoir_with_remaining_rate
#print axioms Luce.section5UnitWeights_assumptions
#print axioms Luce.approximatePermutationPathCode_injective
#print axioms Luce.distinct_approximatePermutationPath_count_le
#print axioms Luce.ghostWindowByOrder_iff_count
#print axioms Luce.ghostWindowByOrder_multiplicity_le
#print axioms Luce.swapClockCopies_measurePreserving
#print axioms Luce.ghostCountKernel_product
#print axioms Luce.finite_insertion_path_countWindow
#print axioms Luce.ghostEntry_eq_density_integral
#print axioms Luce.finite_insertion_path_ennreal
#print axioms Luce.finite_insertion_path_integrable
#print axioms Luce.finite_insertion_path
#print axioms Luce.ghostEntry_row_bound
#print axioms Luce.Section5.rootedCycleEquivPeriodicPoint
#print axioms Luce.Section5.cycleCount_eq_tuple_sum
#print axioms Luce.Section5.cycleCount_symm
#print axioms Luce.Section5.cycleCount_eq_fixedCount
#print axioms Luce.Section5.cycleCount_eq_zero_of_card_lt
#print axioms Luce.Section5.cycleCollection_card
#print axioms Luce.Section5.CycleCollection.disjoint
#print axioms Luce.Section5.rootedCycleCollection_card
#print axioms Luce.ghost_cylinder_bound
#print axioms Luce.ghost_cylinder_product_integrable
#print axioms Luce.added_predecessor
#print axioms Luce.added_predecessor_integrable
#print axioms Luce.ghostColumn_expectation_le
#print axioms Luce.ProfileLimit.weighted_bulk_cylinder
#print axioms Luce.high_rate_density_bound
#print axioms Luce.high_rate_ghostEntry_bound
#print axioms Luce.ProfileLimit.highRateMass_small
#print axioms Luce.ProfileLimit.eventually_moderate_half_mass
#print axioms Luce.cycle_vertex_probability_le_ghost
#print axioms Luce.shortCycleVertexCount_expectation_eq
#print axioms Luce.shortCycleVertexCount_expectation_le
#print axioms Luce.shortCycleVertexCount_integrable
#print axioms Luce.shortCycleVertexCount_eq_filter_period_le
#print axioms Luce.shortCycleVertexCount_inverse
#print axioms Luce.high_rate_cycle_vertex_probability
#print axioms Luce.high_rate_cycle_vertices_bound
#print axioms Luce.ProfileLimit.highCycleExpectation_small
#print axioms Luce.ProfileLimit.high_rate_cycles_vanish
#print axioms Luce.section5_uniform_deleted_arrival
#print axioms Luce.section5_uniform_deleted_remaining
#print axioms Luce.section5_uniform_deleted_quantile
#print axioms Luce.section5_uniform_deleted_denominator
#print axioms Luce.section5_deleted_order_statistics
#print axioms Luce.section5_deleted_gap_rate
#print axioms Luce.ProfileLimit.lowRateDensity_small
#print axioms Luce.lowRateDensity_eq_integral
#print axioms Luce.Section5.rootedCollectionEquivAssignment
#print axioms Luce.Section5.cycleVertex_card
#print axioms Luce.Section5.cycle_factorial_eq_assignment_sum
#print axioms Luce.Section5.rootedCollectionWithinEquivAssignmentWithin
#print axioms Luce.Section5.cutoff_cycle_factorial_eq_assignment_sum
#print axioms Luce.Section5.bulk_cycle_factorial_eq_assignment_sum
#print axioms Luce.integrated_rank_crossing_intensity
#print axioms Luce.beforeCount_occupation_le
#print axioms Luce.ghostWindowVolume_expectation_eq
#print axioms Luce.ghostWindowVolume_expectation_le
#print axioms Luce.ghostWindowLength_integrable
#print axioms Luce.ghostWindowLength_expectation_le
#print axioms Luce.ProfileLimit.interior_ghostWindowLength
#print axioms Luce.ProfileLimit.interior_ghostWindowLength_uniform

-- B. Full binder inspection, including otherwise implicit typeclasses.
set_option pp.explicit true in
#check @Luce.ProfileLimit.moderate_reservoir
set_option pp.explicit true in
#check @Luce.ProfileLimit.moderate_reservoir_with_remaining_rate
set_option pp.explicit true in
#check @Luce.section5UnitWeights_assumptions
set_option pp.explicit true in
#check @Luce.finite_insertion_path
set_option pp.explicit true in
#check @Luce.finite_insertion_path_integrable
set_option pp.explicit true in
#check @Luce.ghostEntry_eq_density_integral
set_option pp.explicit true in
#check @Luce.ghostEntry_row_bound
set_option pp.explicit true in
#check @Luce.Section5.cycleCount_eq_tuple_sum
set_option pp.explicit true in
#check @Luce.Section5.cycleCount_symm
set_option pp.explicit true in
#check @Luce.Section5.cycleCount_eq_fixedCount
set_option pp.explicit true in
#check @Luce.Section5.cycleCollection_card
set_option pp.explicit true in
#check @Luce.Section5.CycleCollection.disjoint
set_option pp.explicit true in
#check @Luce.Section5.rootedCycleCollection_card
set_option pp.explicit true in
#check @Luce.ghost_cylinder_bound
set_option pp.explicit true in
#check @Luce.ghost_cylinder_product_integrable
set_option pp.explicit true in
#check @Luce.added_predecessor
set_option pp.explicit true in
#check @Luce.added_predecessor_integrable
set_option pp.explicit true in
#check @Luce.ghostColumn_expectation_le
set_option pp.explicit true in
#check @Luce.ProfileLimit.weighted_bulk_cylinder
set_option pp.explicit true in
#check @Luce.high_rate_density_bound
set_option pp.explicit true in
#check @Luce.high_rate_ghostEntry_bound
set_option pp.explicit true in
#check @Luce.ProfileLimit.highRateMass_small
set_option pp.explicit true in
#check @Luce.ProfileLimit.eventually_moderate_half_mass
set_option pp.explicit true in
#check @Luce.cycle_vertex_probability_le_ghost
set_option pp.explicit true in
#check @Luce.shortCycleVertexCount_expectation_eq
set_option pp.explicit true in
#check @Luce.shortCycleVertexCount_expectation_le
set_option pp.explicit true in
#check @Luce.shortCycleVertexCount_integrable
set_option pp.explicit true in
#check @Luce.shortCycleVertexCount_eq_filter_period_le
set_option pp.explicit true in
#check @Luce.shortCycleVertexCount_inverse
set_option pp.explicit true in
#check @Luce.high_rate_cycle_vertex_probability
set_option pp.explicit true in
#check @Luce.high_rate_cycle_vertices_bound
set_option pp.explicit true in
#check @Luce.ProfileLimit.highCycleExpectation_small
set_option pp.explicit true in
#check @Luce.ProfileLimit.high_rate_cycles_vanish
set_option pp.explicit true in
#check @Luce.section5_uniform_deleted_arrival
set_option pp.explicit true in
#check @Luce.section5_uniform_deleted_remaining
set_option pp.explicit true in
#check @Luce.section5_uniform_deleted_quantile
set_option pp.explicit true in
#check @Luce.section5_uniform_deleted_denominator
set_option pp.explicit true in
#check @Luce.section5_deleted_order_statistics
set_option pp.explicit true in
#check @Luce.section5_deleted_gap_rate
set_option pp.explicit true in
#check @Luce.ProfileLimit.lowRateDensity_small
set_option pp.explicit true in
#check @Luce.lowRateDensity_eq_integral
set_option pp.explicit true in
#check @Luce.Section5.rootedCollectionEquivAssignment
set_option pp.explicit true in
#check @Luce.Section5.cycleVertex_card
set_option pp.explicit true in
#check @Luce.Section5.cycle_factorial_eq_assignment_sum
set_option pp.explicit true in
#check @Luce.Section5.rootedCollectionWithinEquivAssignmentWithin
set_option pp.explicit true in
#check @Luce.Section5.cutoff_cycle_factorial_eq_assignment_sum
set_option pp.explicit true in
#check @Luce.Section5.bulk_cycle_factorial_eq_assignment_sum
set_option pp.explicit true in
#check @Luce.integrated_rank_crossing_intensity
set_option pp.explicit true in
#check @Luce.beforeCount_occupation_le
set_option pp.explicit true in
#check @Luce.ghostWindowVolume_expectation_eq
set_option pp.explicit true in
#check @Luce.ghostWindowVolume_expectation_le
set_option pp.explicit true in
#check @Luce.ghostWindowLength_integrable
set_option pp.explicit true in
#check @Luce.ghostWindowLength_expectation_le
set_option pp.explicit true in
#check @Luce.ProfileLimit.interior_ghostWindowLength
set_option pp.explicit true in
#check @Luce.ProfileLimit.interior_ghostWindowLength_uniform

-- Expansion of every custom object in the principal theorem types.
#print Luce.Weights
#print Luce.WeightArray
#print Luce.NormalizedWeights
#print Luce.ProfileLimit
#print Luce.ProfileL1Convergence
#print Luce.EndpointAssumption
#print Luce.profileMeasure
#print Luce.stepProfile
#print Luce.moderateReservoir
#print Luce.exponentialRace
#print Luce.pairedExponentialRace
#print Luce.swapClockCopies
#print Luce.clockBeforeCount
#print Luce.GhostWindowByOrder
#print Luce.GhostCountWindow
#print Luce.ghostOrderKernel
#print Luce.ghostCountKernel
#print Luce.ghostEntry
#print Luce.MarkedRankCylinder
#print Luce.ghostColumn
#print Luce.ghostPredecessorSum
#print Luce.insertionPathWeight
#print Luce.predecessorConstant
#print Luce.highRateMass
#print Luce.raceRankPermutation
#print Luce.ghostCycleVertexSum
#print Luce.shortCycleVertexCount
#print Luce.highCycleConstant
#print Luce.highCycleExpectation
#print Luce.deletedEmpiricalArrival
#print Luce.deletedEmpiricalRemainingGe
#print Luce.deletedEmpiricalRemaining
#print Luce.lowRateDensity
#print Luce.Section5.CycleSlot
#print Luce.Section5.CycleVertex
#print Luce.Section5.cycleBlockPermutation
#print Luce.Section5.CycleAssignment
#print Luce.Section5.CycleCollectionWithin
#print Luce.Section5.RootedCycleCollectionWithin
#print Luce.Section5.CycleAssignmentWithin
#print Luce.Section5.cycleOrbitsWithin
#print Luce.Section5.cycleCountWithin
#print Luce.Section5.CutoffCycleCollection
#print Luce.Section5.cycleBlockIndicator
#print Luce.Section5.cycleBlockIndicatorWithin
#print Luce.Section5.bulkCycleLabelSet
#print Luce.Section5.bulkCycleCount
#print Luce.survivingAtRankProbability
#print Luce.ghostWindowVolume
#print Luce.ghostWindowLength
#print Luce.ApproximatePermutationPath
#print Luce.ApproximateClockPath
#print Luce.Section5.IsRootedCycle
#print Luce.Section5.RootedCycle
#print Luce.Section5.cycleVertices
#print Luce.Section5.cycleOrbits
#print Luce.Section5.cycleCount
#print Luce.Section5.cycleAssignmentWeight
#print Luce.Section5.CycleCollection
#print Luce.Section5.CycleRoots
#print Luce.Section5.RootedCycleCollection
