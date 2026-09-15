import Luce.Section5LateReturnSum

noncomputable section
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Move each target's late cutoff back to a common source cutoff while
the predecessor relation is still present. Only then enlarge the pair sum. -/
theorem late_ordered_pairs_le_common_cutoff {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old)
    (T S : Finset (Fin n)) (cut : Fin n → ℝ) (s : ℝ)
    (htime : ∀ v ∈ T, ∀ u ∈ S, u < v → s ≤ cut v) :
    (∑ v ∈ T, ∑ u ∈ S.filter (fun u => u < v),
      lateGhostEntry w ell old hinj u v (cut v) *
        markedReturnWeight (ghostEntry w ell old) k v u) ≤
    ∑ v : Fin n, ∑ u ∈ S, lateGhostEntry w ell old hinj u v s *
      markedReturnWeight (ghostEntry w ell old) k v u := by
  have hreturn (v u : Fin n) : 0 ≤ markedReturnWeight (ghostEntry w ell old) k v u :=
    markedReturnWeight_nonneg _ (fun u v => (ghostEntry_mem_Icc w ell old u v).1) k v u
  have hlate (v u : Fin n) : 0 ≤ lateGhostEntry w ell old hinj u v s :=
    ENNReal.toReal_nonneg
  calc
    _ ≤ ∑ v ∈ T, ∑ u ∈ S.filter (fun u => u < v),
        lateGhostEntry w ell old hinj u v s *
          markedReturnWeight (ghostEntry w ell old) k v u := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_right
        (lateGhostEntry_antitone w ell old hinj u v
          (htime v hv u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2)) (hreturn v u)
    _ ≤ ∑ v ∈ T, ∑ u ∈ S, lateGhostEntry w ell old hinj u v s *
        markedReturnWeight (ghostEntry w ell old) k v u := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun u _ _ => mul_nonneg (hlate v u) (hreturn v u))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun v _ _ => Finset.sum_nonneg fun u _ => mul_nonneg (hlate v u) (hreturn v u))

theorem late_ordered_pairs_bound {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (T S : Finset (Fin n)) (cut : Fin n → ℝ) {b s : ℝ}
    (hb : 0 < b) (hbs : 1 ≤ b*s) (hrate : ∀ u ∈ S, b ≤ w.rate u)
    (htime : ∀ v ∈ T, ∀ u ∈ S, u < v → s ≤ cut v) :
    (∑ v ∈ T, ∑ u ∈ S.filter (fun u => u < v),
      lateGhostEntry w ell old hinj u v (cut v) *
        markedReturnWeight (ghostEntry w ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) * Real.exp (-b*s) :=
  (late_ordered_pairs_le_common_cutoff w ell k old hinj T S cut s htime).trans
    (late_return_sum_le w ell k old hinj hnonneg S hb hbs hrate)

end Luce
