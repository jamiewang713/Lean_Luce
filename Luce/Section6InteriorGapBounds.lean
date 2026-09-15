import Luce.Section6GapOffsets

noncomputable section
namespace Luce.Section6

/-- Bounded deletion and demanded-rank shifts preserve both macroscopic
interior margins. All counts are the actual compacted background counts. -/
theorem shifted_interior_gap_bounds {n r h : ℕ} {eps : ℝ}
    (removed : Finset (Fin n)) (hremoved : removed.card ≤ r)
    (q : Fin (Finset.univ \ removed).card)
    (hlarge : 8*(r : ℝ)+8 ≤ eps*(n : ℝ))
    (hl : eps*(n : ℝ) ≤ (h : ℝ)) (hu : (h : ℝ) ≤ (1-eps)*(n : ℝ))
    (hshift : Nat.dist q.val (h-1) ≤ r+1) :
    (eps/2)*(n : ℝ) ≤ (q.val : ℝ) ∧
      (eps/2)*(n : ℝ) ≤ ((Finset.univ \ removed).card : ℝ)-(q.val : ℝ) := by
  have hh : 8*r+8 ≤ h := by exact_mod_cast hlarge.trans hl
  have hqlo := (shifted_left_gap_bounds hh hshift).2.2
  have hqloR : (h : ℝ) ≤ 2*(q.val : ℝ) := by exact_mod_cast hqlo
  have hqhi : q.val ≤ h+r+1 := by unfold Nat.dist at hshift; omega
  have hqhiR : (q.val : ℝ) ≤ (h : ℝ)+(r : ℝ)+1 := by exact_mod_cast hqhi
  have hdR : (removed.card : ℝ) ≤ r := by exact_mod_cast hremoved
  have hd : removed.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ removed)
  have hcard : ((Finset.univ \ removed).card : ℝ) = (n : ℝ)-(removed.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hd]
  constructor
  · nlinarith
  · rw [hcard]
    nlinarith

end Luce.Section6
