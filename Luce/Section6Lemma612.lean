import Luce.Section6Lemma612Contract
import Luce.Section65PowerContract
import Luce.Section65SpatialContract
import Luce.Section6Critical

/-! Interior-grid sampling, Lemma 6.12. The population, insertion, and
cycle estimates in the completed limit theorems are uniform over both
sampling grids, so their interior specializations give all three assertions. -/

universe u
namespace Luce.Section6

/-- Lemma 6.12: the power-law, spatial, and critical-pole conclusions for
sampling at i/(n+1), including all mean and localization assertions. -/
theorem lemma612 : Lemma612Contract.lemma612.{u} :=
  ⟨powerLaw65 .interior, spatial65 .interior, critical .interior⟩

/-- The complete existing Section 6 contract, on both sampling grids. -/
theorem section6 : SampledProfileContract.section6.{u} :=
  ⟨powerLaw65 .midpoint, spatial65 .midpoint, critical .midpoint, lemma612⟩

end Luce.Section6
