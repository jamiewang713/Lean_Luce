import Luce.Section5ShellContract
import Luce.Section5ContractRepresentation
import Luce.Section5MaximumRoot
import Luce.Section5MaximumExpectation

set_option pp.all true in
#print ShellMigrationContract.section5
#print Luce.cycleTraceIntegrand
#print Luce.cycleTraceIntensity
#print Luce.cycleCountVector
#print Luce.cycleVectorPoissonLaw
#print Luce.cycleVectorTotalVariation
#print Luce.Section5.cycleCount
#print Luce.Section5.cycleOrbits
#print Luce.Section5.bulkCycleCount
#print Luce.Section5.cycleCountWithin
#print Luce.Section5.cycleOrbitsWithin
#print Luce.Section5.cycleMaximum
set_option pp.all true in
#check @Luce.Section5.tailCycleCount_eq_maximum_roots
#print axioms Luce.cyclicProfileMeasure_eq_closed_cube
#print axioms Luce.cycleTraceIntensity_eq_manuscript
#print axioms Luce.cycleVectorPoissonLaw_probability
#print axioms Luce.Section5.cycleMaximum_injective
#print axioms Luce.Section5.maximumCycleRoots_card
#print axioms Luce.Section5.bulkCycleCount_eq_maximum_roots
#print axioms Luce.Section5.tailCycleCount_eq_maximum_roots
#print axioms Luce.Section5.mem_maximumCycleRoots_iff
set_option pp.all true in
#check @Luce.Section5.tailCycleExpectation_eq_maximum_probability_sum
#print axioms Luce.Section5.tailCycleExpectation_eq_maximum_probability_sum
