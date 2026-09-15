import Luce.Section6CycleVertexBound
import Luce.Section6DominationMatrixInterior
import Luce.Section6DominationMatrixSmallRows

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators ENNReal
namespace Luce.Section6

/-- Interior cycle probabilities are O(1/n), for every row size.
The finite exceptional row range is absorbed using probability<=1. -/
theorem PowerProfile.interior_cycle_vertex_probability {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ v : Fin n, eps*(n : ℝ) ≤ (v.val : ℝ)+1 →
      (v.val : ℝ)+1 ≤ (1-eps)*(n : ℝ) →
      (exponentialRace (w n)).real {clocks |
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1} ≤ C/(n : ℝ) := by
  obtain ⟨B, hB, hrow⟩ := hp.domination_matrix_row_bound_all_n (k+1) (k+1) (by omega)
  obtain ⟨D, N, hD, hN, htarget⟩ := hp.domination_matrix_interior_target heps (k+1) (k+1) (by omega)
  refine ⟨D*B^k+N, by positivity, ?_⟩
  intro grid w hw n v hl hu
  have hn : 0 < n := by have := v.isLt; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hlarge : N ≤ (n : ℝ)
  · have ht := cycle_vertex_probability_le_matrix_rows (w n) (le_refl (k+1)) v hB.le
      (show 0 ≤ D/(n : ℝ) by positivity)
      (fun i => hrow grid w hw n i Finset.univ)
      (fun i => htarget grid w hw n hn hlarge i v hl hu)
    have ht' : (exponentialRace (w n)).real {clocks |
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1} ≤ (D*B^k)/(n : ℝ) := by
      simpa only [div_mul_eq_mul_div] using ht
    exact ht'.trans (div_le_div_of_nonneg_right (by linarith) hnR.le)
  · have hprob : (exponentialRace (w n)).real {clocks |
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1} ≤ 1 := by
      have ht := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤)
        (show exponentialRace (w n) {clocks |
          minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1} ≤ 1 from prob_le_one)
      simpa only [measureReal_def, ENNReal.toReal_one] using ht
    apply hprob.trans
    apply (le_div_iff₀ hnR).mpr
    have hpos : 0 < D*B^k := mul_pos hD (pow_pos hB k)
    linarith

end Luce.Section6
