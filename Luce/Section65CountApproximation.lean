import Luce.Section65CoreScale
import Luce.Section65MeanNormalization
import Luce.Section65CorePolynomial

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce.Section6

def CountApprox65 (w : WeightArray) (X Y : ∀ n, Equiv.Perm (Fin n) → ℝ) : Prop :=
  Tendsto (fun n => (∫ clocks, |X n (raceRankPermutation clocks)-Y n (raceRankPermutation clocks)|
    ∂exponentialRace (w n))/Real.sqrt (Real.log (n : ℝ))) atTop (𝓝 0)

theorem countApprox65_of_bound (w : WeightArray) (X Y : ∀ n, Equiv.Perm (Fin n) → ℝ)
    {C : ℝ} (h : ∀ᶠ n in atTop,
      (∫ clocks, |X n (raceRankPermutation clocks)-Y n (raceRankPermutation clocks)|
        ∂exponentialRace (w n)) ≤ C*(1+Real.log (idealCoreLower n : ℝ))) : CountApprox65 w X Y := by
  have ht := one_add_log_core_lower_sqrt_tendsto65.const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) (Real.sqrt_nonneg _))) _ ht
  filter_upwards [h] with n hn
  exact (div_le_div_of_nonneg_right hn (Real.sqrt_nonneg _)).trans_eq (by ring)

theorem countApprox65_of_const_bound (w : WeightArray) (X Y : ∀ n, Equiv.Perm (Fin n) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ᶠ n in atTop,
      (∫ clocks, |X n (raceRankPermutation clocks)-Y n (raceRankPermutation clocks)|
        ∂exponentialRace (w n)) ≤ C) : CountApprox65 w X Y := by
  apply countApprox65_of_bound w X Y
  filter_upwards [h] with n hn
  exact hn.trans (le_mul_of_one_le_right hC (by have := Real.log_natCast_nonneg (idealCoreLower n); linarith))

theorem CountApprox65.normalized {w : WeightArray} {X Y : ∀ n, Equiv.Perm (Fin n) → ℝ}
    (h : CountApprox65 w X Y) {β : ℝ} (hβ : 0 < β) (m : ℕ → ℝ) :
    Tendsto (fun n => ∫ clocks,
      |(X n (raceRankPermutation clocks)-m n)/Real.sqrt (β*Real.log (n : ℝ))-
        (Y n (raceRankPermutation clocks)-m n)/Real.sqrt (β*Real.log (n : ℝ))|
          ∂exponentialRace (w n)) atTop (𝓝 0) := by
  have ht := h.div_const (Real.sqrt β)
  simp only [zero_div] at ht
  convert ht using 1
  funext n
  simp only [← sub_div,sub_sub_sub_cancel_right,abs_div,abs_of_nonneg (Real.sqrt_nonneg _),integral_div]
  rw [Real.sqrt_mul hβ.le,div_div]
  rw [mul_comm (Real.sqrt β)]

theorem CountApprox65.mean {w : WeightArray} {X Y : ∀ n, Equiv.Perm (Fin n) → ℝ}
    (h : CountApprox65 w X Y) {β : ℝ}
    (hY : MeanApprox65 (fun n => ∫ clocks, Y n (raceRankPermutation clocks) ∂exponentialRace (w n)) β) :
    MeanApprox65 (fun n => ∫ clocks, X n (raceRankPermutation clocks) ∂exponentialRace (w n)) β := by
  have he : Tendsto (fun n =>
      ((∫ clocks, X n (raceRankPermutation clocks) ∂exponentialRace (w n))-
       (∫ clocks, Y n (raceRankPermutation clocks) ∂exponentialRace (w n)))/
        Real.sqrt (Real.log (n : ℝ))) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero (fun n => abs_nonneg _) _ h
    intro n
    simp only [Function.comp_apply,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [← integral_sub (integrable_race_permutation_statistic (w n) (X n))
      (integrable_race_permutation_statistic (w n) (Y n))]
    exact abs_integral_le_integral_abs
  have hh := he.add hY
  simp only [zero_add] at hh
  unfold MeanApprox65
  convert hh using 1
  funext n
  dsimp
  ring

theorem coreCount_meanApprox65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (c : CoreCycleCategory) (ha : (cornerBehavior left right c.side).active) {β : ℝ}
    (hm : MeanApprox65 (fun n => coreCategoryIdealMean left right n c) β) :
    MeanApprox65 (fun n => ∫ clocks, (coreCategoryCount (raceRankPermutation clocks) c : ℝ)
      ∂exponentialRace (w n)) β := by
  have he := core_factorial_rapid65 f left right hp grid w hs 1 (fun _ => c) (fun _ => ha)
    (by intro n hn i j hij; exact False.elim (hij (Subsingleton.elim i j))) (fun _ => 1)
  simp only [Fin.prod_univ_one,Nat.descFactorial_one,pow_one] at he
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have hh := (he.tendsto.mul hi).add hm
  simp only [mul_zero,zero_add] at hh
  unfold MeanApprox65
  convert hh using 1
  funext n
  simp only [Function.comp_apply]
  ring

end Luce.Section6
