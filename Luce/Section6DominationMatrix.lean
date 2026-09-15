import Luce.Section6KernelLpOne
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- A finite, nonempty set of every permitted deletion and demanded-gap shift.
The gap bound is only an encoding bound, proved automatic from the shift. -/
def insertionChoices {n : ℕ} (r : ℕ) (j : Fin n) :
    Finset (Finset (Fin n) × Fin (n+r+2)) :=
  Finset.univ.filter (fun z => z.1.card ≤ r ∧ Nat.dist z.2.val j.val ≤ r+1)

theorem insertionChoices_nonempty {n : ℕ} (r : ℕ) (j : Fin n) :
    (insertionChoices r j).Nonempty := by
  refine ⟨(∅, ⟨j.val, by have := j.isLt; omega⟩), ?_⟩
  simp [insertionChoices]

/-- The finite maximum of actual insertion norms, with no assumed estimates. -/
def insertionDominationENN {n : ℕ} (w : Weights n) (r p : ℕ) (i j : Fin n) : ℝ≥0∞ :=
  (insertionChoices r j).sup (fun z =>
    eLpNorm (fun old => (deletedGapKernel w z.1 old i z.2.val).toReal)
      (p : ℝ≥0∞) (exponentialRace w))

/-- The manuscript's deterministic nonnegative matrix, represented in R. -/
def insertionDominationMatrix {n : ℕ} (w : Weights n) (r p : ℕ) (i j : Fin n) : ℝ :=
  (insertionDominationENN w r p i j).toReal

theorem insertionDominationENN_le_one {n : ℕ} (w : Weights n) (r p : ℕ) (i j : Fin n) :
    insertionDominationENN w r p i j ≤ 1 := by
  apply Finset.sup_le
  intro z hz
  exact deleted_kernel_eLpNorm_le_one w z.1 i z.2.val (p : ℝ≥0∞)

theorem insertionDominationMatrix_nonneg {n : ℕ} (w : Weights n) (r p : ℕ) (i j : Fin n) :
    0 ≤ insertionDominationMatrix w r p i j := ENNReal.toReal_nonneg

theorem ofReal_insertionDominationMatrix {n : ℕ} (w : Weights n) (r p : ℕ) (i j : Fin n) :
    ENNReal.ofReal (insertionDominationMatrix w r p i j) = insertionDominationENN w r p i j := by
  apply ENNReal.ofReal_toReal
  exact ne_of_lt ((insertionDominationENN_le_one w r p i j).trans_lt (by simp))

theorem deleted_kernel_le_insertionDominationMatrix {n : ℕ} (w : Weights n)
    (r p : ℕ) (i j : Fin n) (removed : Finset (Fin n)) (q : ℕ)
    (hremoved : removed.card ≤ r) (hshift : Nat.dist q j.val ≤ r+1) :
    eLpNorm (fun old => (deletedGapKernel w removed old i q).toReal)
      (p : ℝ≥0∞) (exponentialRace w) ≤ ENNReal.ofReal (insertionDominationMatrix w r p i j) := by
  rw [ofReal_insertionDominationMatrix]
  have hq : q < n+r+2 := by
    have := j.isLt
    unfold Nat.dist at hshift
    omega
  let z : Finset (Fin n) × Fin (n+r+2) := (removed, ⟨q, hq⟩)
  have hz : z ∈ insertionChoices r j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hremoved, hshift⟩
  unfold insertionDominationENN
  apply Finset.le_sup_of_le hz
  exact le_rfl

theorem insertionDominationMatrix_attained {n : ℕ} (w : Weights n)
    (r p : ℕ) (i j : Fin n) :
    ∃ (removed : Finset (Fin n)) (q : ℕ), removed.card ≤ r ∧ Nat.dist q j.val ≤ r+1 ∧
      ENNReal.ofReal (insertionDominationMatrix w r p i j) =
        eLpNorm (fun old => (deletedGapKernel w removed old i q).toReal)
          (p : ℝ≥0∞) (exponentialRace w) := by
  obtain ⟨z, hz, he⟩ := Finset.exists_mem_eq_sup (insertionChoices r j) (insertionChoices_nonempty r j)
    (fun z => eLpNorm (fun old => (deletedGapKernel w z.1 old i z.2.val).toReal)
      (p : ℝ≥0∞) (exponentialRace w))
  have hc := (Finset.mem_filter.mp hz).2
  exact ⟨z.1, z.2.val, hc.1, hc.2, (ofReal_insertionDominationMatrix w r p i j).trans he⟩

/-- The maximizing choices may vary with the target; the actual row
theorems already quantify such choices, so no cardinality factor is lost. -/
theorem insertionDominationMatrix_row_selection {n : ℕ} (w : Weights n) (r p : ℕ) (i : Fin n) :
    ∃ (removed : Fin n → Finset (Fin n)) (q : Fin n → ℕ),
      ∀ j, (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1 ∧
        ENNReal.ofReal (insertionDominationMatrix w r p i j) =
          eLpNorm (fun old => (deletedGapKernel w (removed j) old i (q j)).toReal)
            (p : ℝ≥0∞) (exponentialRace w) := by
  choose removed q h using (fun j => insertionDominationMatrix_attained w r p i j)
  exact ⟨removed, q, h⟩

end Luce.Section6
