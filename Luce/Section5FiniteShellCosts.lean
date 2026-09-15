import Luce.Section5EarlyTail

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Luce

theorem finite_nonnegative_sum_le_tail (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (J n : ℕ) :
    ENNReal.ofReal (∑ j ∈ Finset.Icc J n, f j) ≤
      ∑' j : ℕ, if J ≤ j then ENNReal.ofReal (f j) else 0 := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hf j)]
  calc
    _ = ∑ j ∈ Finset.Icc J n, if J ≤ j then ENNReal.ofReal (f j) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (Finset.mem_Icc.mp hj).1]
    _ ≤ _ := ENNReal.sum_le_tsum _

theorem early_finite_shell_sum_le_tail (w : WeightArray) (k n J : ℕ) :
    ENNReal.ofReal (∑ j ∈ Finset.Icc J n, ∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostKernel (w n) (k+2) old u v ((j : ℝ) - Real.sqrt j) *
        markedReturnWeight (ghostEntry (w n) (k+2) old) k v u ∂exponentialRace (w n)) ≤
      nonnegativeTail (earlyCycleShellCost w k) n J := by
  apply finite_nonnegative_sum_le_tail
  intro j
  apply integral_nonneg
  intro old
  apply Finset.sum_nonneg
  intro v _
  apply Finset.sum_nonneg
  intro u _
  exact mul_nonneg (earlyGhostKernel_nonneg (w n) (k+2) old u v _)
    (markedReturnWeight_nonneg _ (fun u v => (ghostEntry_mem_Icc (w n) (k+2) old u v).1) k v u)

theorem buffered_finite_shell_sum_le_tail (w : WeightArray) (n J : ℕ) (hJ : 2 ≤ J) :
    ENNReal.ofReal (∑ r ∈ Finset.Icc J n, if hs : (terminalShell n r).Nonempty then
      Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0) ≤
      nonnegativeTail (bufferedShellExpCost w) n J := by
  classical
  have hf (r : ℕ) : 0 ≤ (if hs : (terminalShell n r).Nonempty then
      Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0) := by
    split_ifs <;> positivity
  apply (finite_nonnegative_sum_le_tail _ hf J n).trans_eq
  apply tsum_congr
  intro r
  by_cases hr : J ≤ r
  · simp only [if_pos hr, bufferedShellExpCost, dif_pos (hJ.trans hr)]
    split_ifs <;> simp
  · simp only [if_neg hr]

end Luce
