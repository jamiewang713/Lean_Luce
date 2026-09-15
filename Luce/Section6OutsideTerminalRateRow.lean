import Luce.Section6InteriorRateRow
import Luce.Section6EarlyRateRow

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- All targets outside a fixed terminal block have total insertion norm
O(theta_i). Constants are uniform over sources and bounded deletions/shifts. -/
theorem PowerProfile.outside_terminal_insertion_rate_row {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, eps ≤ (terminalDepth j : ℝ)/(n : ℝ) ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal (C*(w n).rate i) := by
  let t : ℝ := min (1/8) (eps/2)
  have ht : 0 < t := lt_min (by norm_num) (half_pos heps)
  obtain ⟨B, N, hB, hN, hb⟩ := hp.interior_insertion_rate_row ht r p0 hp0
  obtain ⟨D, hD, he⟩ := hp.early_insertion_rate_row p0
  refine ⟨D+B, max N (max (8*(r : ℝ)+8) (2/eps)), add_pos hD hB,
    hN.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge i s removed q p hpp hpp0 hs
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn8 : 8*r+8 ≤ n := by
    have hh := (le_max_left (8*(r : ℝ)+8) (2/eps)).trans ((le_max_right _ _).trans hlarge)
    exact_mod_cast hh
  have hmargin : 2 ≤ eps*(n : ℝ) := by
    have hh := (div_le_iff₀ heps).mp
      ((le_max_right (8*(r : ℝ)+8) (2/eps)).trans ((le_max_right _ _).trans hlarge))
    nlinarith
  classical
  let P : Fin n → Prop := fun j => 8*(j.val+1) ≤ n
  let g : Fin n → ℝ≥0∞ := fun j =>
    eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n))
  have hearly : (∑ j ∈ s.filter P, g j) ≤ ENNReal.ofReal (D*(w n).rate i) := by
    apply he grid w hw n r hn8 i (s.filter P) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨hjP, (hs j hjs).2⟩
  have hinterior : (∑ j ∈ s.filter (fun j => ¬ P j), g j) ≤ ENNReal.ofReal (B*(w n).rate i) := by
    apply hb grid w hw n hn ((le_max_left _ _).trans hlarge) i
      (s.filter (fun j => ¬ P j)) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    obtain ⟨hdepth, hremoved, hshift⟩ := hs j hjs
    have hlowN : n < 8*(j.val+1) := lt_of_not_ge hjP
    have hlow : (n : ℝ) < 8*((j.val : ℝ)+1) := by exact_mod_cast hlowN
    have ht8 : t ≤ 1/8 := min_le_left _ _
    have hte : t ≤ eps/2 := min_le_right _ _
    have hterminal : (terminalDepth j : ℝ) = (n : ℝ)-(j.val : ℝ) := by
      unfold terminalDepth
      rw [Nat.cast_sub j.isLt.le]
    have hh := (le_div_iff₀ hnR).mp hdepth
    rw [hterminal] at hh
    refine ⟨?_, ?_, hremoved, hshift⟩
    · nlinarith [mul_le_mul_of_nonneg_right ht8 hnR.le]
    · nlinarith [mul_le_mul_of_nonneg_right hte hnR.le]
  change (∑ j ∈ s, g j) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s P g]
  have hi := (w n).positive i
  have hh := add_le_add hearly hinterior
  rw [← ENNReal.ofReal_add (mul_pos hD hi).le (mul_pos hB hi).le] at hh
  simpa only [add_mul] using hh

end Luce.Section6
