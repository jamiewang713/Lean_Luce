import Luce.Sections1To7

/-! The approved definition and proposition are reproduced to check the
production theorem against the locked statement by definitional equality.
The proposition below is not assumed: it is proved by `history_predictability`.
-/

open MeasureTheory
universe u

namespace Luce.Section2LockedAudit

def drawHistory {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) : MeasurableSpace Ω :=
  ⨆ j : Fin n, ⨆ (_ : j.val < m),
    MeasurableSpace.comap (fun ω => π ω j) ⊤

def PredictabilityStatement : Prop :=
  ∀ {Ω : Type u} {n : ℕ} (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n)) (k : Fin n),
    Measurable[drawHistory π k.val]
      (fun ω => if k ≤ (π ω).symm k then (1 : ℝ) else 0) ∧
    Measurable[drawHistory π k.val]
      (fun ω => w.total (remaining (π ω) k))

theorem approved_history {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) :
    drawHistory π m = Luce.drawHistory π m := rfl

theorem approved_statement : PredictabilityStatement.{u} := Luce.history_predictability

#print approved_history
#print approved_statement
#print axioms approved_history
#print axioms approved_statement
end Luce.Section2LockedAudit

#print Luce.drawHistory
#print Luce.inverse_ge_iff_no_earlier_draw
#print Luce.measurable_draw_of_lt
#print Luce.measurableSet_label_available
#print Luce.measurable_availability_indicator
#print Luce.measurable_remaining_weight
#print Luce.history_predictability

#print axioms Luce.drawHistory
#print axioms Luce.inverse_ge_iff_no_earlier_draw
#print axioms Luce.measurable_draw_of_lt
#print axioms Luce.measurableSet_label_available
#print axioms Luce.measurable_availability_indicator
#print axioms Luce.measurable_remaining_weight
#print axioms Luce.history_predictability
