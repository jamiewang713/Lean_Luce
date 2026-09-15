import Luce.Section6DominationMatrixInterior
import Luce.Section6DominationMatrixSmallRows

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Uniform middle-target maxima for every row size. The finite small-row
range is absorbed using the proved entry bound M<=1. -/
theorem PowerProfile.domination_matrix_interior_target_all_n {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i j : Fin n), eps*(n : ℝ) ≤ (j.val : ℝ)+1 →
      (j.val : ℝ)+1 ≤ (1-eps)*(n : ℝ) →
      insertionDominationMatrix (w n) r p i j ≤ C/(n : ℝ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hp.domination_matrix_interior_target heps r p hp1
  refine ⟨C+N, add_pos hC hN, ?_⟩
  intro grid w hw n i j hl hu
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hlarge : N ≤ (n : ℝ)
  · exact (hb grid w hw n hn hlarge i j hl hu).trans
      (div_le_div_of_nonneg_right (by linarith) hnR.le)
  · apply (insertionDominationMatrix_le_one (w n) r p i j).trans
    apply (le_div_iff₀ hnR).mpr
    linarith

/-- Uniform middle columns for every row size and any source subset. -/
theorem PowerProfile.domination_matrix_interior_column_all_n {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (j : Fin n), eps*(n : ℝ) ≤ (j.val : ℝ)+1 →
      (j.val : ℝ)+1 ≤ (1-eps)*(n : ℝ) →
    ∀ s : Finset (Fin n), (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨C, hC, hb⟩ := hp.domination_matrix_interior_target_all_n heps r p hp1
  refine ⟨C, hC, ?_⟩
  intro grid w hw n j hl hu s
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt j.isLt)
  have hc : (s.card : ℝ) ≤ n := by
    have hcN : s.card ≤ n := by simpa using s.card_le_univ
    exact_mod_cast hcN
  calc
    _ ≤ ∑ _i ∈ s, C/(n : ℝ) := Finset.sum_le_sum (fun i _ => hb grid w hw n i j hl hu)
    _ = (s.card : ℝ)*(C/(n : ℝ)) := by simp
    _ ≤ (n : ℝ)*(C/(n : ℝ)) := mul_le_mul_of_nonneg_right hc (div_pos hC hnR).le
    _ = C := by field_simp

end Luce.Section6
