import Luce.Section5MaximumReturn

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

theorem marked_return_product_eq_cylinder_sum {n : ℕ} (w : Weights n)
    (k : ℕ) (old : Fin n → ℝ) (v u : Fin n) :
    ghostEntry w (k+2) old u v * markedReturnWeight (ghostEntry w (k+2) old) k v u =
      ∑ t : Fin k → Fin n, ∏ a : Fin (k+2), ghostEntry w (k+2) old
        ((Fin.cons v (Fin.snoc t u) : Fin (k+2) → Fin n) a)
        ((Fin.snoc (Fin.snoc t u) v : Fin (k+2) → Fin n) a) := by
  simp_rw [rootedGhostProduct_eq_forward, Fin.cons_last, Fin.snoc_last]
  unfold markedReturnWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact mul_comm _ _

theorem integrable_marked_return_product {n : ℕ} (w : Weights n)
    (k : ℕ) (v u : Fin n) :
    Integrable (fun old => ghostEntry w (k+2) old u v *
      markedReturnWeight (ghostEntry w (k+2) old) k v u) (exponentialRace w) := by
  simp_rw [marked_return_product_eq_cylinder_sum]
  exact integrable_finsetSum _ (fun t _ => ghost_cylinder_product_integrable w _ _)

/-- The actual retained maximum-cycle probability is bounded by the
integrated marked edge and return paths, with u retained and u < v.
All integrability premises are proved from the canonical race. -/
theorem retained_maximum_cycle_probability_le_return {n : ℕ} (w : Weights n)
    (k : ℕ) (S : Finset (Fin n)) (v : Fin n) :
    (exponentialRace w).real (retainedMaximumCycleEvent (k+1) S v) ≤
      ∫ old, ∑ u : Fin n, if u ∈ S ∧ u < v then
        ghostEntry w (k+2) old u v * markedReturnWeight (ghostEntry w (k+2) old) k v u
        else 0 ∂exponentialRace w := by
  apply (retained_maximum_cycle_probability_le_ghost w (k+1) S v).trans
  apply integral_mono
    (integrable_finsetSum _ (fun t _ => ghost_cylinder_product_integrable w _ _))
    (integrable_finsetSum _ (fun u _ => ?_))
  · intro old
    exact retained_maximum_ghost_sum_le_return w k S old v
  · by_cases hu : u ∈ S ∧ u < v
    · simpa only [if_pos hu] using integrable_marked_return_product w k v u
    · simp only [if_neg hu]
      exact integrable_zero _ _ _

end Luce
