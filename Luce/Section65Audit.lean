import Luce.Section65

universe u
namespace Luce.Section6

theorem powerLaw65_contractCheck (grid : SamplingGrid) : SampledProfileContract.powerLaw.{u} grid :=
  powerLaw65 grid

theorem spatial65_contractCheck (grid : SamplingGrid) : SampledProfileContract.spatial.{u} grid :=
  spatial65 grid

theorem section65_midpoint_contractCheck :
    SampledProfileContract.powerLaw.{u} .midpoint ∧ SampledProfileContract.spatial.{u} .midpoint :=
  ⟨powerLaw65 .midpoint,spatial65 .midpoint⟩

theorem section65_interior_contractCheck :
    SampledProfileContract.powerLaw.{u} .interior ∧ SampledProfileContract.spatial.{u} .interior :=
  ⟨powerLaw65 .interior,spatial65 .interior⟩

end Luce.Section6
