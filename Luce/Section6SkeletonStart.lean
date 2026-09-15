import Luce.Section6GapStart

noncomputable section
namespace Luce.Section6

/-- Remove precisely the selected earlier spacings from the reconstructed
start; S is a finite set of actual background gap indices. -/
def skeletonStart {n : ℕ} (w : Weights n) (sigma : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (q : Fin n) (xi : Fin n → ℝ) : ℝ :=
  ∑ l ∈ (Finset.Iio q).filter (fun l => l ∉ S), xi l / orderedRemainingRate w sigma l

/-- Exact decomposition, without discarding contributions of earlier marks. -/
theorem gap_start_eq_skeleton_add_selected {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (q : Fin n) (xi : Fin n → ℝ) :
    gapStartFromNormalized w sigma q xi = skeletonStart w sigma S q xi +
      ∑ l ∈ (Finset.Iio q).filter (fun l => l ∈ S), xi l / orderedRemainingRate w sigma l := by
  classical
  unfold gapStartFromNormalized skeletonStart
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h : l ∈ S <;> simp [h]

/-- The skeleton is unchanged by arbitrary changes in selected coordinates. -/
theorem skeleton_start_congr_unselected {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (q : Fin n)
    {xi zeta : Fin n → ℝ} (he : ∀ l, l ∉ S → xi l = zeta l) :
    skeletonStart w sigma S q xi = skeletonStart w sigma S q zeta := by
  apply Finset.sum_congr rfl
  intro l hl
  rw [he l (Finset.mem_filter.mp hl).2]

theorem continuous_skeleton_start {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (q : Fin n) :
    Continuous (skeletonStart w sigma S q) := by
  unfold skeletonStart
  fun_prop

theorem skeleton_start_nonneg {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (q : Fin n)
    {xi : Fin n → ℝ} (hxi : ∀ l, 0 ≤ xi l) :
    0 ≤ skeletonStart w sigma S q xi := by
  apply Finset.sum_nonneg
  intro l hl
  exact div_nonneg (hxi l) (orderedRemainingRate_pos w sigma l).le

/-- Applied to actual normalized clocks, this is exactly the manuscript
definition U=T_q minus the selected preceding raw gap lengths. -/
theorem skeleton_start_eq_actual_start_sub_selected {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (q : Fin n) (clocks : Fin n → ℝ) :
    skeletonStart w sigma S q (orderedNormalizedGaps w sigma clocks) =
      previousOrderedTime (fun l => clocks (sigma l)) q -
      ∑ l ∈ (Finset.Iio q).filter (fun l => l ∈ S),
        (clocks (sigma l) - previousOrderedTime (fun k => clocks (sigma k)) l) := by
  have he := gap_start_eq_skeleton_add_selected w sigma S q (orderedNormalizedGaps w sigma clocks)
  rw [gapStartFromNormalized_eq_previous] at he
  simp_rw [← ordered_gap_eq_normalized_div_rate] at he
  linarith

end Luce.Section6
