import Luce.Section6EarlyRateRow
import Luce.Section6SampledRateUpper

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

theorem reciprocal_depth_power_product_le_one {n a beta kappa : ℝ}
    (ha : 0 < a) (han : a ≤ n) (hk : kappa ≤ beta) :
    (n/a)^kappa*(a/n)^beta ≤ 1 := by
  have hn : 0 < n := ha.trans_le han
  have hu : 0 < a/n := div_pos ha hn
  have hrec : n/a = (a/n)⁻¹ := by field_simp
  rw [hrec, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_add hu]
  exact Real.rpow_le_one hu.le ((div_le_one hn).mpr han) (by linarith)

/-- The early-target contribution to the right weighted row bound, retaining
the rate before using its sampled right power asymptotic. -/
theorem PowerProfile.early_right_weighted_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (hk : kappa ≤ beta) (p0 : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 8*r+8 ≤ n →
    ∀ (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < delta →
    ∀ (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, 8*(j.val+1) ≤ n ∧ (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    ENNReal.ofReal (((n : ℝ)/(terminalDepth i : ℝ))^kappa)*
      (∑ j ∈ s, eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, hB, hb⟩ := hp.early_insertion_rate_row p0
  obtain ⟨K, delta, hK, hd, hd1, hr⟩ := hp.right_sampled_rate_upper
  refine ⟨B*K, delta, mul_pos hB hK, hd, hd1, ?_⟩
  intro grid w hw n r hn i hi s removed q p hpp hpp0 hs
  have hrow := hb grid w hw n r hn i s removed q p hpp hpp0 hs
  have hr0 := hr grid w hw n i hi
  have ha : (0 : ℝ) < terminalDepth i := Nat.cast_pos.mpr (terminalDepth_pos i)
  have han : (terminalDepth i : ℝ) ≤ n := by
    exact_mod_cast (show terminalDepth i ≤ n from Nat.sub_le _ _)
  have hpow := reciprocal_depth_power_product_le_one ha han hk
  have hfactor : 0 ≤ ((n : ℝ)/(terminalDepth i : ℝ))^kappa := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ ENNReal.ofReal (((n : ℝ)/(terminalDepth i : ℝ))^kappa)*ENNReal.ofReal (B*(w n).rate i) :=
      mul_le_mul_of_nonneg_left hrow zero_le
    _ = ENNReal.ofReal ((((n : ℝ)/(terminalDepth i : ℝ))^kappa)*(B*(w n).rate i)) :=
      (ENNReal.ofReal_mul hfactor).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h1 := mul_le_mul_of_nonneg_left hr0 (mul_nonneg hfactor hB.le)
      have h2 := mul_le_mul_of_nonneg_left hpow (mul_pos hB hK).le
      nlinarith only [h1, h2]

end Luce.Section6
