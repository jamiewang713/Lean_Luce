import Luce.Section5EarlyTail
import Luce.Section5LateCombined

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- The target-dependent early cutoff agrees with the shell cutoff.
This bounds the full deep-target sum by the already proved shell costs. -/
theorem early_deep_expectation_le_shell_sum {n : ℕ} (w : Weights n)
    (k J : ℕ) (hJ : 1 ≤ J) (S : Finset (Fin n)) :
    (∫ old, ∑ v ∈ deepShellLabels n J, ∑ u ∈ S.filter (fun u => u < v),
      earlyGhostKernel w (k+2) old u v (terminalShellTime v) *
        markedReturnWeight (ghostEntry w (k+2) old) k v u ∂exponentialRace w) ≤
    ∑ j ∈ Finset.Icc J n, ∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostKernel w (k+2) old u v ((j : ℝ) - Real.sqrt j) *
        markedReturnWeight (ghostEntry w (k+2) old) k v u ∂exponentialRace w := by
  have hint (j : ℕ) : Integrable (fun old => ∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostKernel w (k+2) old u v ((j : ℝ) - Real.sqrt j) *
        markedReturnWeight (ghostEntry w (k+2) old) k v u) (exponentialRace w) :=
    integrable_finsetSum _ (fun v _ => integrable_finsetSum _
      (fun u _ => integrable_early_return_product w k v u _))
  rw [← integral_finsetSum _ (fun j _ => hint j)]
  apply integral_mono
    (integrable_finsetSum _ (fun v _ => integrable_finsetSum _
      (fun u _ => integrable_early_return_product w k v u _)))
    (integrable_finsetSum _ (fun j _ => hint j))
  intro old
  let F := fun v : Fin n => ∑ u : Fin n,
    earlyGhostKernel w (k+2) old u v (terminalShellTime v) *
      markedReturnWeight (ghostEntry w (k+2) old) k v u
  have hp (v u : Fin n) : 0 ≤ earlyGhostKernel w (k+2) old u v (terminalShellTime v) *
      markedReturnWeight (ghostEntry w (k+2) old) k v u :=
    mul_nonneg (earlyGhostKernel_nonneg w (k+2) old u v _)
      (markedReturnWeight_nonneg _ (fun u v => (ghostEntry_mem_Icc w (k+2) old u v).1) k v u)
  have hcover (v : Fin n) (hv : v ∈ deepShellLabels n J) :
      v ∈ (∅ : Finset (Fin n)) ∨ ∃ j ∈ Finset.Icc J n, v ∈ terminalShell n j := by
    have hvJ := (Finset.mem_filter.mp hv).2
    have hmem := mem_terminalShellNumber v (hJ.trans hvJ)
    exact Or.inr ⟨terminalShellNumber v,
      Finset.mem_Icc.mpr ⟨hvJ, shell_index_le_row ⟨v, hmem⟩⟩, hmem⟩
  calc
    _ ≤ ∑ v ∈ deepShellLabels n J, F v := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun u _ _ => hp v u)
    _ ≤ ∑ j ∈ Finset.Icc J n, ∑ v ∈ terminalShell n j, F v := by
      simpa only [Finset.sum_empty, zero_add] using
        finite_cover_sum_le (deepShellLabels n J) ∅ (Finset.Icc J n) (terminalShell n)
          F (fun v => Finset.sum_nonneg fun u _ => hp v u) hcover
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro v hv
      simp only [F, terminalShellTime, terminalShellNumber_eq_of_mem hv]

end Luce
