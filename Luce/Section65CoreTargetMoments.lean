import Luce.Section65FiniteCategories
import Luce.Section65MeanNormalization
import Luce.Section65AffineMoments

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Luce.Section6

theorem core_target_mixed_moments65 {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (left right : EndpointBehavior) (hp : PowerProfile f left right)
    (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (c : ι → CoreCycleCategory)
    (ha : ∀ i, (cornerBehavior left right (c i).side).active)
    (hd : FiniteCategoriesDisjoint65 c)
    (β : ι → ℝ) (hβ : ∀ i, 0 < β i)
    (hm : ∀ i, MeanApprox65 (fun n => coreCategoryIdealMean left right n (c i)) (β i))
    (r : ι → ℕ) :
    Tendsto (fun n => ∫ clocks, ∏ i : ι,
      (((coreCategoryCount (raceRankPermutation clocks) (c i) : ℝ)-β i*Real.log (n : ℝ))/
        Real.sqrt (β i*Real.log (n : ℝ)))^(r i) ∂exponentialRace (w n)) atTop
      (𝓝 (∏ i, gaussianMoment65 1 (r i))) := by
  let a (n : ℕ) (i : ι) := Real.sqrt (coreCategoryIdealMean left right n (c i))/
    Real.sqrt (β i*Real.log (n : ℝ))
  let b (n : ℕ) (i : ι) := (coreCategoryIdealMean left right n (c i)-β i*Real.log (n : ℝ))/
    Real.sqrt (β i*Real.log (n : ℝ))
  have ht := race_affine_moments65 w
    (fun _ R i => normalizedCoreCategory65 left right R (c i))
    (core_normalized_finite_moments65 f left right hp grid w hs c ha hd β hβ hm)
    a b (fun i => (hm i).scale (hβ i)) (fun i => (hm i).shift (hβ i)) r
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n in atTop, ∀ i : ι, 0 < coreCategoryIdealMean left right n (c i) := by
    rw [Filter.eventually_all]
    intro i
    exact ((hm i).diverges (hβ i)).eventually_gt_atTop 0
  apply ht.congr'
  filter_upwards [hpos,hlog.eventually_gt_atTop 0] with n hn hl
  apply integral_congr_ae
  filter_upwards [] with clocks
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  exact (normalization_affine65 (hn i) (mul_pos (hβ i) hl)
    (coreCategoryCount (raceRankPermutation clocks) (c i) : ℝ)).symm

end Luce.Section6
