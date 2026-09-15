import Luce.Section65PowerContract
import Luce.Section65SpatialContract

universe u
namespace Luce.Section6

/-- Section 6.5: power-law cycle-count CLTs and logarithmic spatial localization,
with precisely the original sampled-profile contracts on either grid. -/
theorem section65 :
    (∀ grid, SampledProfileContract.powerLaw.{u} grid) ∧
    (∀ grid, SampledProfileContract.spatial.{u} grid) := ⟨powerLaw65,spatial65⟩

end Luce.Section6
