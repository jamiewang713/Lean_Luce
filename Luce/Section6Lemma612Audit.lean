import Luce.Section6Lemma612

universe u
namespace Luce.Section6

/-- Check against the three original interior-grid contracts directly. -/
theorem lemma612_contractCheck :
    SampledProfileContract.powerLaw.{u} .interior ∧
      SampledProfileContract.spatial.{u} .interior ∧
      SampledProfileContract.critical.{u} .interior := lemma612

/-- Separate check of the unchanged, complete Section 6 target. -/
theorem section6_contractCheck : SampledProfileContract.section6.{u} := section6

end Luce.Section6
