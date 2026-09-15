import Luce.Section5LateKernel

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Split the actual retained maximum-cycle probability sum at arbitrary
target cutoffs. Every probability and return weight is the existing one. -/
theorem retained_maximum_probability_sum_le_time_split {n : ℕ} (w : Weights n)
    (k : ℕ) (S T : Finset (Fin n)) (cut : Fin n → ℝ) :
    (∑ v ∈ T, (exponentialRace w).real (retainedMaximumCycleEvent (k+1) S v)) ≤
      (∫ old, ∑ v ∈ T, ∑ u ∈ S.filter (fun u => u < v),
        earlyGhostKernel w (k+2) old u v (cut v) *
          markedReturnWeight (ghostEntry w (k+2) old) k v u ∂exponentialRace w) +
      (∫ old, ∑ v ∈ T, ∑ u ∈ S.filter (fun u => u < v),
        lateGhostKernel w (k+2) old u v (cut v) *
          markedReturnWeight (ghostEntry w (k+2) old) k v u ∂exponentialRace w) := by
  let E := fun (v : Fin n) (old : Fin n → ℝ) =>
    ∑ u ∈ S.filter (fun u => u < v), earlyGhostKernel w (k+2) old u v (cut v) *
      markedReturnWeight (ghostEntry w (k+2) old) k v u
  let L := fun (v : Fin n) (old : Fin n → ℝ) =>
    ∑ u ∈ S.filter (fun u => u < v), lateGhostKernel w (k+2) old u v (cut v) *
      markedReturnWeight (ghostEntry w (k+2) old) k v u
  have hE (v : Fin n) : Integrable (E v) (exponentialRace w) :=
    integrable_finsetSum _ (fun u _ => integrable_early_return_product w k v u _)
  have hL (v : Fin n) : Integrable (L v) (exponentialRace w) :=
    integrable_finsetSum _ (fun u _ => integrable_late_return_product w k v u _)
  have hpoint (v : Fin n) :
      (exponentialRace w).real (retainedMaximumCycleEvent (k+1) S v) ≤
        (∫ old, E v old ∂exponentialRace w) + ∫ old, L v old ∂exponentialRace w := by
    apply (retained_maximum_cycle_probability_le_return w k S v).trans_eq
    rw [← integral_add (hE v) (hL v)]
    apply integral_congr_ae
    filter_upwards [] with old
    dsimp [E, L]
    rw [← Finset.sum_add_distrib]
    have hsum : (∑ u ∈ S.filter (fun u => u < v),
        (earlyGhostKernel w (k+2) old u v (cut v) *
            markedReturnWeight (ghostEntry w (k+2) old) k v u +
          lateGhostKernel w (k+2) old u v (cut v) *
            markedReturnWeight (ghostEntry w (k+2) old) k v u)) =
        ∑ u ∈ S.filter (fun u => u < v), ghostEntry w (k+2) old u v *
          markedReturnWeight (ghostEntry w (k+2) old) k v u := by
      apply Finset.sum_congr rfl
      intro u _
      unfold lateGhostKernel
      ring
    rw [hsum]
    simp [Finset.sum_filter, ite_and]
  have h := Finset.sum_le_sum (fun v (_ : v ∈ T) => hpoint v)
  rw [Finset.sum_add_distrib, ← integral_finsetSum T (fun v _ => hE v),
    ← integral_finsetSum T (fun v _ => hL v)] at h
  exact h

end Luce
