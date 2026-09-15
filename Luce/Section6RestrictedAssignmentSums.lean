import Luce.Section6CategoryCycleCounting

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem finite_indicator_sum_eq_subtype {α : Type*} [Fintype α]
    (P : α → Prop) (f : α → ℝ) [DecidablePred P] :
    (∑ x, if P x then f x else 0) = ∑ x : {x // P x}, f x.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

def restrictedEmbeddingEquiv {α ν : Type*}
    (Q : ν → α → Prop) (P : (ν → α) → Prop)
    (hP : ∀ x, P x → ∀ v, Q v (x v)) :
    {e : ν ↪ α // P e} ≃
      {x : ∀ v, {a // Q v a} // Function.Injective (fun v => (x v).val) ∧ P (fun v => (x v).val)} where
  toFun e := ⟨fun v => ⟨e.val v, hP e.val e.property v⟩, e.val.injective, e.property⟩
  invFun x := ⟨⟨fun v => (x.val v).val, x.property.1⟩, x.property.2⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; funext v; rfl

/-- Restricting every vertex to its specified core commutes exactly with
the finite sum over globally injective labelled assignments. -/
theorem restricted_embedding_sum {α ν : Type*} [Fintype α] [Fintype ν] [DecidableEq α] [DecidableEq ν]
    (Q : ν → α → Prop) (P : (ν → α) → Prop)
    (hP : ∀ x, P x → ∀ v, Q v (x v)) (f : (ν → α) → ℝ)
    [DecidablePred P] [∀ v, DecidablePred (Q v)] :
    (∑ e : ν ↪ α, if P e then f e else 0) =
      ∑ x : ∀ v, {a // Q v a},
        if Function.Injective (fun v => (x v).val) ∧ P (fun v => (x v).val) then
          f (fun v => (x v).val) else 0 := by
  calc
    _ = ∑ e : {e : ν ↪ α // P e}, f e.val :=
      finite_indicator_sum_eq_subtype (fun e : ν ↪ α => P e) (fun e => f e)
    _ = ∑ x : {x : ∀ v, {a // Q v a} //
        Function.Injective (fun v => (x v).val) ∧ P (fun v => (x v).val)},
        f (fun v => (x.val v).val) :=
      Fintype.sum_equiv (restrictedEmbeddingEquiv Q P hP) _ _ (fun _ => rfl)
    _ = _ := (finite_indicator_sum_eq_subtype
      (fun x : ∀ v, {a // Q v a} => Function.Injective (fun v => (x v).val) ∧ P (fun v => (x v).val))
      (fun x => f (fun v => (x v).val))).symm

end Luce.Section6
