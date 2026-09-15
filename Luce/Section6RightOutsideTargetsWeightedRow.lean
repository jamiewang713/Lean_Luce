import Luce.Section6OutsideTerminalRateRow
import Luce.Section6EarlyRightWeightedRow

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- For right-corner sources, the O(theta_i) mass outside any fixed right
target block absorbs (n/a)^kappa. The power rate bound is derived internally. -/
theorem PowerProfile.right_outside_targets_scaled_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa eps : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk : kappa ≤ beta) (heps : 0 < eps) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C delta N : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < delta →
    ∀ (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, eps ≤ (terminalDepth j : ℝ)/(n : ℝ) ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    ENNReal.ofReal (((n : ℝ)/(terminalDepth i : ℝ))^kappa)*
      (∑ j ∈ s, eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, N, hB, hN, hb⟩ := hp.outside_terminal_insertion_rate_row heps r p0 hp0
  obtain ⟨K, delta, hK, hd, hd1, hr⟩ := hp.right_sampled_rate_upper
  refine ⟨B*K, delta, N, mul_pos hB hK, hd, hd1, hN, ?_⟩
  intro grid w hw n hn hlarge i hi s removed q p hpp hpp0 hs
  have hrow := hb grid w hw n hn hlarge i s removed q p hpp hpp0 hs
  have hr0 := hr grid w hw n i hi
  have ha : (0 : ℝ) < terminalDepth i := Nat.cast_pos.mpr (terminalDepth_pos i)
  have han : (terminalDepth i : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n i.val)
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

/-- The manuscript's target-dependent right weight follows from the
stronger constant (n/a)^kappa weight when kappa is nonnegative. -/
theorem PowerProfile.right_outside_targets_weighted_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa eps : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk0 : 0 ≤ kappa) (hk : kappa ≤ beta) (heps : 0 < eps) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C delta N : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < delta →
    ∀ (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, eps ≤ (terminalDepth j : ℝ)/(n : ℝ) ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨C, delta, N, hC, hd, hd1, hN, hb⟩ := hp.right_outside_targets_scaled_row hk heps r p0 hp0
  refine ⟨C, delta, N, hC, hd, hd1, hN, ?_⟩
  intro grid w hw n hn hlarge i hi s removed q p hpp hpp0 hs
  have ha : (0 : ℝ) < terminalDepth i := Nat.cast_pos.mpr (terminalDepth_pos i)
  apply le_trans _ (hb grid w hw n hn hlarge i hi s removed q p hpp hpp0 hs)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : (terminalDepth j : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n j.val)
  have hratio := div_le_div_of_nonneg_right hjn ha.le
  have hweight := Real.rpow_le_rpow (by positivity) hratio hk0
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hweight) zero_le

end Luce.Section6
