import Luce.Section5EarlyKernel
import Luce.EndpointShellBufferLimit

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Luce

/-- Expected early marked-return contribution of one nonempty target shell.
An empty shell has zero contribution. -/
def earlyCycleShellCost (w : WeightArray) (k n j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
    earlyGhostKernel (w n) (k+2) old u v ((j : ℝ) - Real.sqrt j) *
      markedReturnWeight (ghostEntry (w n) (k+2) old) k v u
    ∂exponentialRace (w n))

theorem earlyCycleShellCost_le {w : WeightArray} (hnorm : NormalizedWeights w)
    (k n j : ℕ) (hj : (64 + 2 * (k+2+1))^2 ≤ j) :
    earlyCycleShellCost w k n j ≤ ENNReal.ofReal ((2*(k+2)+1 : ℕ)^(k+1) : ℝ) *
      ENNReal.ofReal (Real.exp (1 - Real.sqrt j)) := by
  by_cases hshell : (terminalShell n j).Nonempty
  · rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (early_ghost_return_expectation hnorm n j k hshell hj)
  · simp [earlyCycleShellCost, Finset.not_nonempty_iff_eq_empty.mp hshell]

theorem earlyCycleShellTail_le {w : WeightArray} (hnorm : NormalizedWeights w)
    (k n J : ℕ) (hJ : (64 + 2 * (k+2+1))^2 ≤ J) :
    nonnegativeTail (earlyCycleShellCost w k) n J ≤
      ENNReal.ofReal ((2*(k+2)+1 : ℕ)^(k+1) : ℝ) *
        ∑' j : ℕ, if J ≤ j then ENNReal.ofReal (Real.exp (1 - Real.sqrt j)) else 0 := by
  rw [nonnegativeTail, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases hj : J ≤ j
  · simpa only [if_pos hj] using earlyCycleShellCost_le hnorm k n j (hJ.trans hj)
  · simp only [if_neg hj, mul_zero, le_refl]

/-- Early contributions vanish uniformly in the row. This uniform bound is
a derived estimate; the endpoint shell assumption itself is not strengthened. -/
theorem earlyCycleShellTail_small {w : WeightArray} (hnorm : NormalizedWeights w)
    (k : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ n : ℕ, nonnegativeTail (earlyCycleShellCost w k) n J < ε := by
  let C := ENNReal.ofReal ((2*(k+2)+1 : ℕ)^(k+1) : ℝ)
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := C) (by simp [C]) hε.ne'
  have he := ennreal_tendsto_tail_sum summable_buffer_error.tsum_ofReal_ne_top
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp
    ((ENNReal.tendsto_nhds_zero.mp he) δ (by exact_mod_cast hδ))
  let J := max J₀ ((64 + 2 * (k+2+1))^2)
  refine ⟨J, fun n => ?_⟩
  apply lt_of_le_of_lt (earlyCycleShellTail_le hnorm k n J (le_max_right _ _))
  calc
    _ ≤ C * δ := mul_le_mul' (le_refl C) (hJ₀ J (le_max_left _ _))
    _ < ε := by simpa only [mul_comm] using hδε

theorem earlyCycleShellTail_limit {w : WeightArray} (hnorm : NormalizedWeights w)
    (k : ℕ) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (earlyCycleShellCost w k) n J)
      atTop) atTop (𝓝 0) := by
  apply (nonnegativeTail_limit_iff _).mpr
  intro ε hε
  obtain ⟨J, hJ⟩ := earlyCycleShellTail_small hnorm k hε
  exact ⟨J, Filter.Eventually.of_forall hJ⟩

end Luce
