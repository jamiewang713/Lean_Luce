import Luce.Section6SeparatedOrderSum

noncomputable section
open Function
namespace Luce.Section6

/-- The left effective gap depth differs from its demanded one-based
rank by at most the number of marks, with no separation premise needed. -/
theorem sorted_gap_left_displacement {n s r : ℕ} (hs : s ≤ r)
    (j : Fin s → Fin n) (hj : Injective j) (e : Fin s) :
    |(sortedMarkedGapIndex j e : ℝ) -
      (cornerDistance .left (j (Tuple.sort j e)) : ℝ)| ≤ r := by
  have he := sortedMarkedGapIndex_add j hj e
  have hlow : (j (Tuple.sort j e)).val+1 ≤ sortedMarkedGapIndex j e+r := by omega
  have hhigh : sortedMarkedGapIndex j e ≤ (j (Tuple.sort j e)).val+1+r := by omega
  have hl : ((j (Tuple.sort j e)).val : ℝ)+1 ≤ (sortedMarkedGapIndex j e : ℝ)+r := by
    exact_mod_cast hlow
  have hh : (sortedMarkedGapIndex j e : ℝ) ≤ ((j (Tuple.sort j e)).val : ℝ)+1+r := by
    exact_mod_cast hhigh
  simp only [cornerDistance, Nat.cast_add, Nat.cast_one]
  rw [abs_le]
  constructor <;> linarith

/-- The right effective depth is N-q, where N is the actual undeleted
cardinality. Its displacement from the original terminal depth is at most r. -/
theorem sorted_gap_right_displacement {n s r : ℕ} (hs : s ≤ r)
    (u j : Fin s → Fin n) (hu : Injective u) (hj : Injective j) (e : Fin s) :
    |((Finset.univ \ Finset.univ.image (u ∘ Tuple.sort j)).card : ℝ) -
      (sortedMarkedGapIndex j e : ℝ) -
      (cornerDistance .right (j (Tuple.sort j e)) : ℝ)| ≤ r := by
  have hsn : s ≤ n := by simpa using Fintype.card_le_of_injective u hu
  have hcard : (Finset.univ.image (u ∘ Tuple.sort j)).card = s := by
    rw [Finset.card_image_of_injective _ (hu.comp (Tuple.sort j).injective),
      Finset.card_univ, Fintype.card_fin]
  have hN : (Finset.univ \ Finset.univ.image (u ∘ Tuple.sort j)).card = n-s := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hcard]
  have he := sortedMarkedGapIndex_add j hj e
  have heR : (sortedMarkedGapIndex j e : ℝ)+(e.val : ℝ) = ((j (Tuple.sort j e)).val : ℝ) := by
    exact_mod_cast he
  have helo : (0 : ℝ) ≤ e.val := Nat.cast_nonneg _
  have hehi : (e.val : ℝ) ≤ s := by exact_mod_cast e.isLt.le
  have hsr : (s : ℝ) ≤ r := Nat.cast_le.mpr hs
  rw [hN]
  simp only [cornerDistance, Nat.cast_sub hsn, Nat.cast_sub (j (Tuple.sort j e)).isLt.le]
  rw [abs_le]
  constructor <;> linarith only [heR, helo, hehi, hsr]

end Luce.Section6
