import Luce.Section6LeftEndpointWeightedRow
import Luce.Section6RightEndpointWeightedRow
import Luce.Section6EarlyRateRow
import Luce.Section6InactiveInsertionRow

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Uniform left-target row, covering either permitted endpoint behavior. -/
theorem PowerProfile.left_endpoint_uniform_row {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C delta N : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1/2 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, ((j.val : ℝ)+1)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  cases left with
  | power c alpha eta =>
    have ha : 0 < alpha := zero_lt_one.trans hp.2.2.1.2.1
    simpa only [Real.rpow_zero, ENNReal.ofReal_one, one_mul] using
      hp.left_endpoint_weighted_insertion_row (kappa := 0) le_rfl ha r p0 hp0
  | finite c =>
    obtain ⟨B, hB, hb⟩ := hp.early_insertion_rate_row p0
    obtain ⟨M, hM, hm⟩ := hp.global_upper_of_left_finite
    refine ⟨B*M, 1/8, 8*(r : ℝ)+8, mul_pos hB hM, by norm_num, by norm_num, by positivity, ?_⟩
    intro grid w hw n hn hlarge i s removed q p hpp hpp0 hs
    have hn8 : 8*r+8 ≤ n := by exact_mod_cast hlarge
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hrow := hb grid w hw n r hn8 i s removed q p hpp hpp0 (by
      intro j hj
      obtain ⟨hsmall, hremoved, hshift⟩ := hs j hj
      have hh := (div_le_iff₀ hnR).mp hsmall
      have hh' : 8*((j.val : ℝ)+1) ≤ n := by linarith
      exact ⟨by exact_mod_cast hh', hremoved, hshift⟩)
    apply hrow.trans
    apply ENNReal.ofReal_le_ofReal
    have hi : (w n).rate i ≤ M := by rw [hw n i]; exact hm _ (samplePoint_mem grid i)
    exact mul_le_mul_of_nonneg_left hi hB.le

/-- Uniform right-target row, including inactive terminal targets and all
natural gap conventions. No positive endpoint power is imposed in the finite case. -/
theorem PowerProfile.right_endpoint_uniform_row {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C delta N : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1/2 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, (terminalDepth j : ℝ)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  cases right with
  | power c beta eta =>
    have hb : 0 < beta := hp.2.2.2.1.2.1
    simpa only [Real.rpow_zero, ENNReal.ofReal_one, one_mul] using
      hp.right_endpoint_weighted_insertion_row (kappa := 0) le_rfl hb r p0 hp0
  | finite c =>
    obtain ⟨C, N, hC, hN, hb⟩ := hp.inactive_right_insertion_row r p0 hp0
    refine ⟨C, 1/16384, (N : ℝ), hC, by norm_num, by norm_num, Nat.cast_pos.mpr hN, ?_⟩
    intro grid w hw n hn hlarge i s removed q p hpp hpp0 hs
    have hnN : N ≤ n := by exact_mod_cast hlarge
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    apply hb grid w hw n hnN i s removed q p hpp hpp0
    intro j hj
    obtain ⟨hsmall, hremoved, hshift⟩ := hs j hj
    have hh := (div_le_iff₀ hnR).mp hsmall
    have hh' : 16384*(terminalDepth j : ℝ) ≤ n := by linarith
    exact ⟨by exact_mod_cast hh', hremoved, hshift⟩

end Luce.Section6
