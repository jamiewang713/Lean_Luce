import Luce.Section6Critical

universe u
namespace Luce.Section6

theorem critical_contractCheck (grid : SamplingGrid) : SampledProfileContract.critical.{u} grid :=
  critical grid

theorem critical_midpoint_contractCheck : SampledProfileContract.critical.{u} .midpoint :=
  critical .midpoint

theorem critical_interior_contractCheck : SampledProfileContract.critical.{u} .interior :=
  critical .interior

end Luce.Section6
