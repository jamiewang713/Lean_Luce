import Luce.Section5EarlyWindowProbability
import Luce.Section5MaximumReturnExpectation

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce

/-- On the rare early-survivor event we may bound even the entire marked
return contribution, before imposing predecessor or retention restrictions. -/
theorem early_shell_return_expectation {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j k : ℕ) (hshell : (terminalShell n j).Nonempty)
    (hj : (64 + 2 * (k + 2 + 1)) ^ 2 ≤ j) :
    (∫ old in earlyGhostSurvivorEvent n (shellMax n j hshell) (k+2)
        ((j : ℝ) - Real.sqrt j),
      ∑ v ∈ terminalShell n j, ∑ u : Fin n,
        ghostEntry (w n) (k+2) old u v *
          markedReturnWeight (ghostEntry (w n) (k+2) old) k v u
      ∂exponentialRace (w n)) ≤
      (2*(k+2)+1 : ℕ)^(k+1) * Real.exp (1 - Real.sqrt j) := by
  let C : ℝ := (2*(k+2)+1 : ℕ)
  let E := earlyGhostSurvivorEvent n (shellMax n j hshell) (k+2)
    ((j : ℝ) - Real.sqrt j)
  have hint : Integrable (fun old => ∑ v ∈ terminalShell n j, ∑ u : Fin n,
      ghostEntry (w n) (k+2) old u v *
        markedReturnWeight (ghostEntry (w n) (k+2) old) k v u)
      (exponentialRace (w n)) :=
    integrable_finsetSum _ (fun v _ => integrable_finsetSum _
      (fun u _ => integrable_marked_return_product (w n) k v u))
  have hbound : ∀ᵐ old ∂(exponentialRace (w n)).restrict E,
      (∑ v ∈ terminalShell n j, ∑ u : Fin n,
        ghostEntry (w n) (k+2) old u v *
          markedReturnWeight (ghostEntry (w n) (k+2) old) k v u) ≤
        ((terminalShell n j).card : ℝ) * C^(k+1) := by
    filter_upwards [ae_restrict_of_ae (exponentialRace_nonnegative_background (w n))]
      with old hnonneg
    have hp (u v : Fin n) : 0 ≤ ghostEntry (w n) (k+2) old u v :=
      (ghostEntry_mem_Icc (w n) (k+2) old u v).1
    calc
      _ ≤ ∑ _v ∈ terminalShell n j, C^(k+1) := by
        apply Finset.sum_le_sum
        intro v _
        calc
          _ ≤ ∑ u, markedReturnWeight (ghostEntry (w n) (k+2) old) k v u := by
            apply Finset.sum_le_sum
            intro u _
            exact mul_le_of_le_one_left (markedReturnWeight_nonneg _ hp k v u)
              (ghostEntry_mem_Icc (w n) (k+2) old u v).2
          _ ≤ _ := markedReturnWeight_sum_le _ hp C (by positivity)
            (ghostEntry_row_bound (w n) (k+2) old hnonneg) k v
      _ = _ := by simp
  calc
    _ ≤ ∫ _old in E, ((terminalShell n j).card : ℝ) * C^(k+1)
        ∂exponentialRace (w n) :=
      integral_mono_ae hint.restrict (integrable_const _) hbound
    _ = C^(k+1) * (((terminalShell n j).card : ℝ) *
        (exponentialRace (w n)).real E) := by
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (early_ghost_shell_probability hnorm n j (k+2) hshell hj) (by positivity)

end Luce
