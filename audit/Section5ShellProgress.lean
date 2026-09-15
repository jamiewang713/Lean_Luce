import Luce.Section5InteriorLowRates
import Luce.Section5ShellMarkedEdge

-- Progress audit only: no Section 5 main theorem or contract check is claimed.
set_option pp.all true in
#check @Luce.ProfileLimit.interior_low_rate_cycles_vanish
#print Luce.interiorLowCycleExpectation
#print Luce.shortCycleVertexCount
#print Luce.lowRateDensity
#print Luce.highCycleExpectation
#print axioms Luce.ProfileLimit.high_rate_cycles_vanish
#print axioms Luce.ProfileLimit.interiorLowCycleExpectation_bound
#print axioms Luce.ProfileLimit.interiorLowCycleExpectation_small
#print axioms Luce.ProfileLimit.interior_low_rate_cycles_vanish
#print Luce.markedReturnWeight
set_option pp.all true in
#check @Luce.ghost_marked_edge_bound
#print axioms Luce.markedReturnWeight_sum_le
#print axioms Luce.ghost_marked_edge_bound
