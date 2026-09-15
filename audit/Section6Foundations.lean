import Luce.Section6Contract
import Luce.Section6EndpointBounds
import Luce.Section6PopulationDerivatives

set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false

#print Luce.Section6.PowerProfile
#print Luce.Section6.LeftBehavior
#print Luce.Section6.RightBehavior
#print Luce.Section6.CriticalProfile
#print Luce.Section6.PowerExpansion
#print Luce.Section6.SampledRates
#print Luce.Section6.SpatialIndex
#print SampledProfileContract.powerLaw
#print SampledProfileContract.spatial
#print SampledProfileContract.critical
#print SampledProfileContract.section6
#print axioms Luce.Section6.samplePoint_mem
#print axioms Luce.Section6.sampledWeights_sampled
#print axioms Luce.Section6.samplePoint_rev
#print axioms Luce.Section6.PowerExpansion.relative_error_tendsto
#print axioms Luce.Section6.PowerExpansion.eventually_comparable
#print axioms Luce.Section6.PowerProfile.right_eventually_comparable
#print axioms Luce.Section6.PowerProfile.left_eventually_comparable
#print axioms Luce.Section6.CriticalProfile.eventually_comparable
#print axioms Luce.Section6.populationG_eq_one_sub_H
#print axioms Luce.Section6.populationH_deletion_bound
#print axioms Luce.Section6.populationG_deletion_bound
#print axioms Luce.Section6.populationD_one_deletion_bound
#print axioms Luce.Section6.populationD_hasDerivAt
#print axioms Luce.Section6.populationH_hasDerivAt
#print axioms Luce.Section6.populationG_hasDerivAt
#print axioms Luce.Section6.finite_average_deletion
#print axioms Luce.Section6.finite_average_deletion_bound
#print axioms Luce.Section6.rateKernel_le_exp_neg_one_div
#print axioms Luce.Section6.survivalKernel_hasDerivAt_time
