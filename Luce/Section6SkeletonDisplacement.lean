import Luce.Section6SkeletonProduct

noncomputable section
namespace Luce.Section6

/-- Every earlier gap has at least the current remaining weight. This
comparison is chronological and therefore also applies across corners. -/
theorem ordered_remaining_rate_antitone {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) : Antitone (orderedRemainingRate w sigma) := by
  intro a b hab
  unfold orderedRemainingRate
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.trans (Finset.mem_filter.mp hk).2⟩
  · intro k _ _
    exact (w.positive _).le

/-- Removing selected spacings perturbs the actual starting time by at
most the sum of their normalized lengths divided by the current weight.
No endpoint assumption or independence premise is required. -/
theorem skeleton_displacement_bound {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (q : Fin n)
    (xi : Fin n → ℝ) (hx : ∀ g ∈ S, 0 ≤ xi g) :
    0 ≤ gapStartFromNormalized w sigma q xi - skeletonStart w sigma S q xi ∧
    gapStartFromNormalized w sigma q xi - skeletonStart w sigma S q xi ≤
      (∑ g ∈ S, xi g)/orderedRemainingRate w sigma q := by
  rw [gap_start_eq_skeleton_add_selected_indices w sigma S q xi, add_sub_cancel_left]
  refine ⟨Finset.sum_nonneg (fun g hg => div_nonneg (hx g (Finset.mem_filter.mp hg).1)
    (orderedRemainingRate_pos w sigma g).le), ?_⟩
  calc
    _ ≤ ∑ g ∈ S.filter (fun g => g < q), xi g/orderedRemainingRate w sigma q := by
      apply Finset.sum_le_sum
      intro g hg
      exact div_le_div_of_nonneg_left (hx g (Finset.mem_filter.mp hg).1)
        (orderedRemainingRate_pos w sigma q)
        (ordered_remaining_rate_antitone w sigma (Finset.mem_filter.mp hg).2.le)
    _ ≤ ∑ g ∈ S, xi g/orderedRemainingRate w sigma q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro g hg _
      exact div_nonneg (hx g hg) (orderedRemainingRate_pos w sigma q).le
    _ = _ := (Finset.sum_div S (fun g => xi g) _).symm

end Luce.Section6
