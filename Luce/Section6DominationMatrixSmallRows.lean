import Luce.Section6DominationMatrixRows

noncomputable section
open scoped ENNReal BigOperators
namespace Luce.Section6

theorem insertionDominationMatrix_le_one {n : ℕ} (w : Weights n)
    (r p : ℕ) (i j : Fin n) : insertionDominationMatrix w r p i j ≤ 1 := by
  have h := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞)
    (insertionDominationENN_le_one w r p i j)
  simpa only [insertionDominationMatrix, ENNReal.toReal_one] using h

/-- A finite-row bound requiring no asymptotic profile input. -/
theorem insertionDominationMatrix_row_le_size {n : ℕ} (w : Weights n)
    (r p : ℕ) (i : Fin n) (s : Finset (Fin n)) :
    (∑ j ∈ s, insertionDominationMatrix w r p i j) ≤ (n : ℝ) := by
  have hc : (s.card : ℝ) ≤ n := by
    have hcN : s.card ≤ n := by simpa using s.card_le_univ
    exact_mod_cast hcN
  calc
    _ ≤ ∑ _j ∈ s, (1 : ℝ) := Finset.sum_le_sum (fun j _ => insertionDominationMatrix_le_one w r p i j)
    _ ≤ (n : ℝ) := by simpa using hc

/-- Bounded rows for every row size, absorbing the finitely many small rows
into the constant without altering the matrix. -/
theorem PowerProfile.domination_matrix_row_bound_all_n {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (r p : ℕ) (hp1 : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n) (s : Finset (Fin n)),
      (∑ j ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨C, N, hC, hN, hb⟩ := hp.domination_matrix_row_bound r p hp1
  refine ⟨C+N, add_pos hC hN, ?_⟩
  intro grid w hw n i s
  by_cases hn : N ≤ (n : ℝ)
  · exact (hb grid w hw n (Nat.zero_lt_of_lt i.isLt) hn i s).trans (by linarith)
  · exact (insertionDominationMatrix_row_le_size (w n) r p i s).trans (by linarith)

end Luce.Section6
