import Luce.Section65ActiveCorners
import Luce.Section65CoreTargetMoments
import Luce.Section65IdealMean

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Luce.Section6

abbrev PowerIndex65 (left right : EndpointBehavior) (L : ℕ) := ActiveCorner65 left right × Fin L

theorem powerCategories_disjoint65 (left right : EndpointBehavior) (L : ℕ) :
    FiniteCategoriesDisjoint65 (fun z : PowerIndex65 left right L => cornerCoreCategory65 z.1.val z.2.val) := by
  intro n hn i j hij hs hk
  exact False.elim (hij (Prod.ext (Subtype.ext hs) (Fin.ext hk)))

theorem power_core_target_moments65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (L : ℕ) (r : PowerIndex65 left right L → ℕ) :
    Tendsto (fun n => ∫ clocks, ∏ z : PowerIndex65 left right L,
      (((coreCategoryCount (raceRankPermutation clocks) (cornerCoreCategory65 z.1.val z.2.val) : ℝ)-
        cornerCoefficient z.1.val (cornerBehavior left right z.1.val) z.2.val*Real.log (n : ℝ))/
        Real.sqrt (cornerCoefficient z.1.val (cornerBehavior left right z.1.val) z.2.val*Real.log (n : ℝ)))^(r z)
          ∂exponentialRace (w n)) atTop (𝓝 (∏ z, gaussianMoment65 1 (r z))) := by
  exact core_target_mixed_moments65 f left right hp grid w hs
    (fun z : PowerIndex65 left right L => cornerCoreCategory65 z.1.val z.2.val) (fun z => z.1.property)
    (powerCategories_disjoint65 left right L)
    (fun z => cornerCoefficient z.1.val (cornerBehavior left right z.1.val) z.2.val)
    (fun z => hp.cornerCoefficient_pos65 _ z.1.property _)
    (fun z => idealTrace_meanApprox65 f left right hp _ z.1.property _) r

end Luce.Section6
