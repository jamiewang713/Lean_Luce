import Luce.Section5DeletedGaps
import Mathlib.Data.Fin.Tuple.Sort

/-! # Sorting marked ranks and exact deleted-gap indices -/

noncomputable section
open Function
open scoped BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

lemma markedRankCylinder_comp_perm {n r : ℕ} (u j : Fin r → Fin n)
    (e : Equiv.Perm (Fin r)) (old : Fin n → ℝ) :
    MarkedRankCylinder (u ∘ e) (j ∘ e) old ↔ MarkedRankCylinder u j old := by
  constructor
  · intro h a
    simpa using h (e.symm a)
  · intro h a
    exact h (e a)

lemma markedImage_comp_perm {n r : ℕ} (u : Fin r → Fin n) (e : Equiv.Perm (Fin r)) :
    Finset.univ.image (u ∘ e) = Finset.univ.image u := by
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨e a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨e.symm a, by simpa using ha⟩

lemma strictMono_sorted_markedRanks {n r : ℕ} (j : Fin r → Fin n) (hj : Injective j) :
    StrictMono (j ∘ Tuple.sort j) :=
  (Tuple.monotone_sort j).strictMono_of_injective (hj.comp (Tuple.sort j).injective)

/-- A strictly increasing sequence of natural rank positions has at least
`a` entries before its `a`th value. This proves subtraction is not truncated. -/
lemma index_le_of_strictMono_ranks {n r : ℕ} (j : Fin r → Fin n)
    (hj : StrictMono j) (a : Fin r) : a.val ≤ (j a).val := by
  have hs : (Finset.Iio a).image j ⊆ Finset.Iio (j a) := by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Iio.mpr (hj (Finset.mem_Iio.mp hb))
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hj.injective, Fin.card_Iio, Fin.card_Iio] at hc
  exact hc

def sortedMarkedGapIndex {n r : ℕ} (j : Fin r → Fin n) (a : Fin r) : ℕ :=
  (j (Tuple.sort j a)).val - a.val

lemma sortedMarkedGapIndex_add {n r : ℕ} (j : Fin r → Fin n) (hj : Injective j) (a : Fin r) :
    sortedMarkedGapIndex j a + a.val = (j (Tuple.sort j a)).val :=
  Nat.sub_add_cancel (index_le_of_strictMono_ranks _ (strictMono_sorted_markedRanks j hj) a)

/-- Macroscopic rank separation eventually implies this finite condition:
rank distances at least `r` force all deleted gap numbers to be distinct. -/
lemma sortedMarkedGapIndex_strictMono {n r : ℕ} (j : Fin r → Fin n) (hj : Injective j)
    (hsep : ∀ a b, a ≠ b → r ≤ Nat.dist (j a).val (j b).val) :
    StrictMono (sortedMarkedGapIndex j) := by
  intro a b hab
  have he : Tuple.sort j a ≠ Tuple.sort j b := fun h => hab.ne ((Tuple.sort j).injective h)
  have hs := hsep (Tuple.sort j a) (Tuple.sort j b) he
  have hsort : (j (Tuple.sort j a)).val < (j (Tuple.sort j b)).val :=
    strictMono_sorted_markedRanks j hj hab
  have ha := sortedMarkedGapIndex_add j hj a
  have hb := sortedMarkedGapIndex_add j hj b
  unfold Nat.dist at hs
  omega

/-- Finite bulk margin excludes the terminal deleted gap. -/
lemma sortedMarkedGapIndex_lt_complement {n r : ℕ} (u j : Fin r → Fin n)
    (hu : Injective u) (hbulk : ∀ a, (j a).val + r < n) (a : Fin r) :
    sortedMarkedGapIndex j a < (Finset.univ \ Finset.univ.image u).card := by
  rw [compactMarkedClocks_card u hu]
  have hb := hbulk (Tuple.sort j a)
  unfold sortedMarkedGapIndex
  omega

/-- Exact marked insertion identity with sorting and gap indices derived
from the original arbitrary injective target tuple. -/
theorem markedRankCylinder_probability_eq_sortedGapProduct {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : Injective j)
    (hsep : ∀ a b, a ≠ b → r ≤ Nat.dist (j a).val (j b).val) :
    exponentialRace w {old | MarkedRankCylinder u j old} =
      ∫⁻ old, ∏ a, deletedGapKernel w (Finset.univ.image u) old
        (u (Tuple.sort j a)) (sortedMarkedGapIndex j a) ∂exponentialRace w := by
  have h := markedRankCylinder_probability_eq_deletedGapProduct w (u ∘ Tuple.sort j)
    (j ∘ Tuple.sort j) (hu.comp (Tuple.sort j).injective)
    (strictMono_sorted_markedRanks j hj) (sortedMarkedGapIndex j)
    (sortedMarkedGapIndex_strictMono j hj hsep) (sortedMarkedGapIndex_add j hj)
  simpa only [markedRankCylinder_comp_perm, markedImage_comp_perm, Function.comp_apply] using h

end Luce
