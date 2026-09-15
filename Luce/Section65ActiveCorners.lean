import Luce.Section65CoefficientPositivity
import Luce.Section6CoreCategoryDefinitions

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

abbrev ActiveCorner65 (left right : EndpointBehavior) :=
  {side : Corner // (cornerBehavior left right side).active}

instance activeCornerFintype65 (left right : EndpointBehavior) : Fintype (ActiveCorner65 left right) := by
  classical
  infer_instance

theorem sum_activeCorners65 (left right : EndpointBehavior) (f : Corner → ℝ) :
    (∑ s : ActiveCorner65 left right, f s.val) =
      (if left.active then f .left else 0)+(if right.active then f .right else 0) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun s => (cornerBehavior left right s).active))
    (by simp) f]
  change (∑ s ∈ ({Corner.left,Corner.right} : Finset Corner).filter
    (fun s => (cornerBehavior left right s).active), f s) = _
  calc
    _ = ∑ s ∈ ({Corner.left,Corner.right} : Finset Corner),
        if (cornerBehavior left right s).active then f s else 0 :=
      Finset.sum_filter (fun s => (cornerBehavior left right s).active) f
    _ = _ := by
      by_cases hl : left.active <;> by_cases hr : right.active <;> simp [cornerBehavior,hl,hr]

theorem inactive_coefficient_zero65 (side : Corner) (behavior : EndpointBehavior)
    (ha : ¬ behavior.active) (k : ℕ) : cornerCoefficient side behavior k = 0 := by
  cases behavior with
  | finite c => rfl
  | power c γ η => exact False.elim (ha trivial)

theorem sum_active_coefficients65 (left right : EndpointBehavior) (k : ℕ) :
    (∑ s : ActiveCorner65 left right, cornerCoefficient s.val (cornerBehavior left right s.val) k) =
      totalCoefficient left right k := by
  rw [sum_activeCorners65 left right (fun s => cornerCoefficient s (cornerBehavior left right s) k)]
  dsimp [cornerBehavior,totalCoefficient]
  by_cases hl : left.active <;> by_cases hr : right.active <;>
    simp [hl,hr,inactive_coefficient_zero65]

def cornerCoreCategory65 (side : Corner) (k : ℕ) : CoreCycleCategory := ⟨side,k,.all⟩

def totalCoreCount65 {n : ℕ} (R : Equiv.Perm (Fin n)) (left right : EndpointBehavior) (k : ℕ) : ℝ :=
  ∑ s : ActiveCorner65 left right, (coreCategoryCount R (cornerCoreCategory65 s.val k) : ℝ)

end Luce.Section6
