import Luce.ShellMigrationFoundations
import Luce.Section4Theorem
import Luce.ShellContractCheck

/-! This checks definitions and completed foundations only. The closed
`section4_contractCheck` must be added only after its actual proof exists. -/
set_option pp.all true in
#print ShellMigrationContract.section4
#print Luce.Weights
#print Luce.WeightArray
#print Luce.NormalizedWeights
#print Luce.ProfileLimit
#print Luce.ProfileL1Convergence
#print Luce.profileMeasure
#print Luce.stepProfile
#print Luce.UniformEndpointAssumption
#print Luce.EndpointAssumption
#print Luce.terminalDepth
#print Luce.terminalShell
#print Luce.shellFloor
#print Luce.shellCost
#print Luce.shellTailCost
#print Luce.EndpointShellAssumption
#print Luce.Weights.mass
#print Luce.profileQuantile
#print Luce.profileDiagonal
#print Luce.profileF
#print Luce.profileH
#print Luce.profileD
#print Luce.rateKernel
#print Luce.survivalKernel
#print Luce.interiorDensityMeasure
#print Luce.FinitePointMeasure
#print Luce.fixedPoints
#print Luce.interiorFixedPoints
#print Luce.observedPointMeasure
#print Luce.section3Location
#print Luce.fixedPointCount
#print Luce.fixedPointCountLaw
#print Luce.poissonProbabilityMeasure
#print Luce.probabilityTotalVariation
#print Luce.finitePoissonLaw
#print Luce.poissonMixture
#print Luce.iidPointLaw
#print axioms ShellMigrationContract.old_fullIntensity_underlying
#print axioms Luce.shell_index_le_row
#print axioms Luce.shellFloor_attained
#print axioms Luce.shellTailCost_eq_sum
#print axioms Luce.shellTailCost_ne_top
#print axioms Luce.endpointShellAssumption_iff_eventually
#print axioms Luce.meanSurvivors_jensen
#print axioms Luce.NormalizedWeights.meanSurvivors_jensen

set_option pp.all true in
#print Luce.block_endpoint_capacity
set_option pp.all true in
#print Luce.EndpointShellAssumption.buffered_Q_raw
set_option pp.all true in
#print Luce.section4_count_poisson_general
#print axioms Luce.UniformEndpointAssumption.shell
#print axioms Luce.integral_capacity_kernel
#print axioms Luce.integrable_capacity_kernel
#print axioms Luce.capacity_kernel_antitone
#print axioms Luce.bernoulli_block_lower_tail
#print axioms Luce.removed_survivor_probability_le
#print axioms Luce.sum_fullSurvivorProbability_le_one
#print axioms Luce.exponentialRace_block_capacity
#print axioms Luce.block_fixedPoint_expectation_eq
#print axioms Luce.block_endpoint_capacity
#print axioms Luce.EndpointShellAssumption.buffered_exp
#print axioms Luce.EndpointShellAssumption.buffered_Q
#print axioms Luce.EndpointShellAssumption.buffered_Q_raw
-- These are historical uniform-endpoint results, not migrated main theorems.
#print axioms Luce.section4_full_poisson_general
#print axioms Luce.section4_count_poisson_general
set_option pp.all true in
#print Luce.section4_main_poisson_general
#print axioms Luce.section4_main_poisson_general

-- Shell implementation and the independent closed contract check.
set_option pp.all true in
#check @Luce.Shell.section4_main_poisson_general
set_option pp.all true in
#check @section4_contractCheck
#print section4_contractCheck
#print Luce.Shell.fullIntensity
set_option pp.all true in
#check @Luce.EndpointShellAssumption.expectation_tightness
set_option pp.all true in
#check @Luce.EndpointShellAssumption.probability_tightness
#print axioms Luce.shell_survivor_buffer
#print axioms Luce.shell_early_envelope
#print axioms Luce.shell_block_expectation_le
#print axioms Luce.EndpointShellAssumption.expectation_shells
#print axioms Luce.spatial_tail_expectation_le_shells
#print axioms Luce.EndpointShellAssumption.expectation_tightness
#print axioms Luce.EndpointShellAssumption.probability_tightness
#print axioms Luce.Shell.intensity_test_bound
#print axioms Luce.Shell.section4_full_intensity_finite
#print axioms Luce.Shell.section4_profileDiagonal_integrable
#print axioms Luce.Shell.section4_main_poisson_general
#print axioms section4_contractCheck
#print axioms Luce.Shell.fullIntensity_eq_uniform
