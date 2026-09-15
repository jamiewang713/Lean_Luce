import Luce.Section5ShellContractCheck
import Luce.Section4ShellContractCheck
import Luce.Section5CycleShellContractCheck

set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false

#print Luce.Weights
#print Luce.WeightArray
#print Luce.Weights.mass
#print Luce.NormalizedWeights
#print Luce.stepProfile
#print Luce.profileMeasure
#print Luce.ProfileL1Convergence
#print Luce.ProfileLimit
#print Luce.EndpointAssumption
#print Luce.UniformEndpointAssumption
#print Luce.terminalDepth
#print Luce.terminalShell
#print Luce.shellFloor
#print Luce.shellCost
#print Luce.shellTailCost
#print Luce.EndpointShellAssumption
#print Luce.survivalKernel
#print Luce.rateKernel
#print Luce.profileH
#print Luce.profileF
#print Luce.profileD
#print Luce.profileQuantile
#print Luce.cyclicProfileDensity
#print Luce.cyclicProfileMeasure
#print Luce.Section5.cycleVertices
#print Luce.Section5.cycleOrbits
#print Luce.Section5.cycleCount
#print Luce.cycleCountVector
#print Luce.cycleTraceIntegrand
#print Luce.cycleTraceIntensity
#print Luce.cycleVectorPoissonLaw
#print Luce.cycleVectorTotalVariation
#print Luce.cycleCountVector_raceDraw_eq_rank
#print Luce.cycleVectorTotalVariation_eq_countable
#print Luce.section5_main_general
#print ShellMigrationContract.section5
#print section5_contractCheck

#print axioms Luce.section5_main_general
#print axioms section5_contractCheck
#print axioms Luce.EndpointShellAssumption.cycle_shell_tightness
#print axioms cycleShell_contractCheck
#print axioms Luce.EndpointShellAssumption.cycle_trace_integrable
#print axioms Luce.EndpointShellAssumption.bulk_intensity_tendsto
#print axioms Luce.bulk_joint_factorial_moments
#print axioms Luce.bulk_cycle_point_probability_limit
#print axioms Luce.EndpointShellAssumption.cycle_point_probability_limit
#print axioms Luce.CountableLaw.tendsto_probabilityTotalVariation_of_singletons
#print axioms Luce.CountableLaw.tendsto_bounded_integrals_of_totalVariation
#print axioms Luce.EndpointShellAssumption.cycle_vector_totalVariation
#print axioms Luce.EndpointShellAssumption.cycle_vector_weak
#print axioms Luce.cycleCountVector_raceDraw_eq_rank
#print axioms Luce.luce_cycle_vector_map_eq
#print axioms Luce.luce_cycle_test_integral_eq
#print axioms Luce.Shell.section4_main_poisson_general
#print axioms section4_contractCheck
