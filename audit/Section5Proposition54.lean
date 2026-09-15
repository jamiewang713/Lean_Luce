import Luce.Section5ExceptionalLow

/- Separate statement audit. Print the actual elaborated binders and
expand every custom mathematical hypothesis and event of the target. -/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

#check @Luce.section5_proposition54
#check @Luce.ProfileLimit.low_rate_cycles_vanish
#check @Luce.ProfileLimit.lowCycleExpectation_small
#check @Luce.ProfileLimit.lowCycleExpectation_bound
#check @Luce.ProfileLimit.bounded_cycle_probability_uniform
#check @Luce.shortCycleVertexCount_le_high_add_avoiding
#check @Luce.bounded_ghost_cycle_sum_le
#check @Luce.ghostEntry_le_rate_mul_length
#check @Luce.ghostWindowVolume_ne_top_of_interior

#print Luce.Weights
#print Luce.NormalizedWeights
#print Luce.ProfileLimit
#print Luce.ProfileL1Convergence
#print Luce.EndpointAssumption
#print Luce.shortCycleVertexCount
#print Luce.shortCycleVertexCountAvoiding
#print Luce.OrbitAvoids
#print Luce.boundedCycleEvent
#print Luce.highCycleExpectation
#print Luce.lowCycleExpectation
#print Luce.lowRateDensity
#print Luce.ghostWindowLength
#print Luce.ghostWindowVolume
#print Luce.ghostEntry
#print Luce.ghostOrderKernel
#print Luce.GhostWindowByOrder

#print axioms Luce.section5_proposition54
#print axioms Luce.ProfileLimit.low_rate_cycles_vanish
#print axioms Luce.ProfileLimit.lowCycleExpectation_small
#print axioms Luce.ProfileLimit.lowCycleExpectation_bound
#print axioms Luce.ProfileLimit.bounded_cycle_probability_uniform
#print axioms Luce.shortCycleVertexCount_expectation_le_high_add_avoiding
#print axioms Luce.shortCycleVertexCount_le_high_add_avoiding
#print axioms Luce.bounded_cycle_probability_le_ghost
#print axioms Luce.bounded_ghost_cycle_sum_le
#print axioms Luce.ghostEntry_le_rate_mul_length
#print axioms Luce.ghostWindowVolume_ne_top_of_interior
#print axioms Luce.forwardPathWeight_sum_le
