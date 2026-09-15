import Luce.Section6CoreFamilyDomination

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem core_family_ideal_nonneg {s n A B : ℕ} (side : Fin s → Corner)
    (behavior : Fin s → EndpointBehavior) (k : Fin s → ℕ)
    (P : ∀ c, (Fin (k c+1) → Fin n) → Prop)
    (hK : ∀ c (a b : Fin n), 0 ≤ localIdealKernel (side c) (behavior c)
      (cornerDistance (side c) a) (cornerDistance (side c) b))
    (x : CollisionAssignment n A B side k) : 0 ≤ coreFamilyIdealWeight side behavior k P x := by
  apply Finset.prod_nonneg
  intro c _
  split_ifs
  · exact Finset.prod_nonneg (fun j _ => hK c _ _)
  · exact le_rfl

theorem core_family_ideal_le_product {s n A B : ℕ} (side : Fin s → Corner)
    (behavior : Fin s → EndpointBehavior) (k : Fin s → ℕ)
    (P : ∀ c, (Fin (k c+1) → Fin n) → Prop)
    (hK : ∀ c (a b : Fin n), 0 ≤ localIdealKernel (side c) (behavior c)
      (cornerDistance (side c) a) (cornerDistance (side c) b))
    (x : CollisionAssignment n A B side k) :
    coreFamilyIdealWeight side behavior k P x ≤ varyingCycleFamilyWeight side k
      (fun c a b => localIdealKernel (side c) (behavior c)
        (cornerDistance (side c) a) (cornerDistance (side c) b)) x := by
  apply Finset.prod_le_prod
  · intro c _
    split_ifs
    · exact Finset.prod_nonneg (fun j _ => hK c _ _)
    · exact le_rfl
  · intro c _
    split_ifs
    · exact le_rfl
    · exact Finset.prod_nonneg (fun j _ => hK c _ _)

theorem core_family_ideal_of_injective {s n A B : ℕ} (side : Fin s → Corner)
    (behavior : Fin s → EndpointBehavior) (k : Fin s → ℕ)
    (P : ∀ c, (Fin (k c+1) → Fin n) → Prop)
    (x : CollisionAssignment n A B side k) (hx : Function.Injective (collisionLabel x)) :
    coreFamilyIdealWeight side behavior k P x =
      if ∀ c, P c (fun j => (x c j).val) then varyingCycleFamilyWeight side k
        (fun c a b => localIdealKernel (side c) (behavior c)
          (cornerDistance (side c) a) (cornerDistance (side c) b)) x else 0 := by
  unfold coreFamilyIdealWeight
  simp_rw [core_family_block_injective x hx, true_and]
  have hh := Fintype.prod_ite_zero (p := fun c => P c (fun j => (x c j).val))
    (f := fun c => idealCycleWeight (side c) (behavior c) (k c)
      (fun j => cornerDistance (side c) (x c j).val))
  apply hh.trans
  by_cases h : ∀ c, P c (fun j => (x c j).val)
  · exact (if_pos h).trans (if_pos h).symm
  · exact (if_neg h).trans (if_neg h).symm

end Luce.Section6
