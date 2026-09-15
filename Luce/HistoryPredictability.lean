import Luce.DrawHistory
import Luce.DrawHistoryPermutation
import Mathlib.MeasureTheory.Group.Arithmetic

/-! # Predictability from the actual draw history

Source: `fixed_points.tex:569-579`, the measurability assertion following
`eq:predictable-p`. The history definition and final statement were approved
in `proposals/Section2Predictability.lean`. No probability law is assumed:
the information in the preceding draws already determines availability and
remaining weight. This does not assert the conditional-probability identity.
-/

open MeasureTheory
universe u

namespace Luce

/-- Each already observed coordinate is measurable for the draw history. -/
lemma measurable_draw_of_lt {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) {m : ℕ} (j : Fin n) (hj : j.val < m) :
    Measurable[drawHistory π m, (⊤ : MeasurableSpace (Fin n))] (fun ω => π ω j) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

/-- Any label remains precisely when no preceding draw has selected it.
This supplies the measurable summands in the remaining-weight formula. -/
lemma measurableSet_label_available {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (k i : Fin n) :
    MeasurableSet[drawHistory π k.val] {ω | k ≤ (π ω).symm i} := by
  let : MeasurableSpace Ω := drawHistory π k.val
  have heq : {ω | k ≤ (π ω).symm i} =
      ⋂ j : Fin n, ⋂ (_ : j < k), {ω | π ω j ≠ i} := by
    ext ω
    simpa only [Set.mem_ofPred_eq, Set.mem_iInter] using
      inverse_ge_iff_no_earlier_draw (π ω) k i
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  exact (measurable_draw_of_lt π j hj)
    (show MeasurableSet[(⊤ : MeasurableSpace (Fin n))] {a | a ≠ i} from trivial)

/-- The availability indicator is measurable before draw `k.val + 1`. -/
lemma measurable_availability_indicator {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (k : Fin n) :
    Measurable[drawHistory π k.val]
      (fun ω => if k ≤ (π ω).symm k then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_label_available π k k) measurable_const measurable_const

/-- The remaining weight is measurable for exactly the same pre-draw history. -/
lemma measurable_remaining_weight {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (k : Fin n) :
    Measurable[drawHistory π k.val]
      (fun ω => w.total (remaining (π ω) k)) := by
  classical
  simp only [Weights.total, remaining, Finset.sum_filter]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_label_available π k i) measurable_const measurable_const

/-- The exact approved Section 2 predictability statement. -/
theorem history_predictability {Ω : Type u} {n : ℕ} (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n)) (k : Fin n) :
    Measurable[drawHistory π k.val]
      (fun ω => if k ≤ (π ω).symm k then (1 : ℝ) else 0) ∧
    Measurable[drawHistory π k.val]
      (fun ω => w.total (remaining (π ω) k)) :=
  ⟨measurable_availability_indicator π k, measurable_remaining_weight w π k⟩

end Luce
