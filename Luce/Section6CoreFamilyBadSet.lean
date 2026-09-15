import Luce.Section6NonmoderateFamilies

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

def coreFamilyBad {s n A B : ℕ} (side : Fin s → Corner) (behavior : Fin s → EndpointBehavior)
    (k : Fin s → ℕ) (v : ℝ) (D : ℕ) (x : CollisionAssignment n A B side k) : Prop :=
  (∃ p q : CollisionSlot k, p ≠ q ∧ collisionNearby D p q x) ∨
    ∃ p, cycleEdgeNonmoderate side behavior k v p x

theorem core_family_bad_sum_bound {s n A B L : ℕ} (D : ℕ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (side : Fin s → Corner)
    (behavior : Fin s → EndpointBehavior) (k : Fin s → ℕ) (hk : ∀ c, k c+1 ≤ L)
    (F : Fin s → Fin n → Fin n → ℝ) (hF : ∀ c a b, 0 ≤ F c a b)
    {C v eta : ℝ} (kappa : Fin s → ℝ) (hC : 1 ≤ C) (hv : 0 < v)
    (hkap : ∀ c, 0 < kappa c) (hg : ∀ c, 0 < localCornerExponent (behavior c))
    (heta : ∀ c, eta ≤ v*kappa c/localCornerExponent (behavior c))
    (hrow : ∀ c a, ∑ b, F c a b ≤ C)
    (hw : ∀ c a, (∑ b, (cornerRowRatio (side c) (cornerDistance (side c) a)
      (cornerDistance (side c) b))^(kappa c)*F c a b) ≤ C)
    (htarget : ∀ c (b : CollisionCore n A B (side c)) a,
      F c a b.val ≤ C/(cornerDistance (side c) b.val : ℝ)) :
    (∑ x : CollisionAssignment n A B side k,
      if coreFamilyBad side behavior k v D x then varyingCycleFamilyWeight side k F x else 0) ≤
      (s*L : ℕ)^2*(C^L)^2*(2*(2*(D : ℝ)+1)/(A : ℝ))*
        (C^L*(1+Real.log ((B : ℝ)/A)))^(s-1) +
      (s*L : ℕ)*((C^L*(1+Real.log ((B : ℝ)/A)))/(A : ℝ)^eta)*
        (C^L*(1+Real.log ((B : ℝ)/A)))^(s-1) := by
  have hcol := varying_cycle_family_collision_bound D hA hAB side k hk F hF hC hrow htarget
  have hmod := nonmoderate_cycle_family_sum hA hAB side behavior k hk F hF kappa hC hv hkap hg heta hrow hw htarget
  have he : (∑ x : CollisionAssignment n A B side k,
      if ∃ p q : CollisionSlot k, p ≠ q ∧ collisionNearby D p q x then
        varyingCycleFamilyWeight side k F x else 0) =
      collisionUnionSum (varyingCycleFamilyWeight (A := A) (B := B) side k F) D := by
    unfold collisionUnionSum
    rw [Finset.sum_filter]
  have hh := finite_or_weight_sum (varyingCycleFamilyWeight (A := A) (B := B) side k F)
    (varying_cycle_family_nonneg side k F hF)
    (fun x => ∃ p q : CollisionSlot k, p ≠ q ∧ collisionNearby D p q x)
    (fun x => ∃ p, cycleEdgeNonmoderate side behavior k v p x)
  rw [he] at hh
  have hchange : (∑ x : CollisionAssignment n A B side k,
      if coreFamilyBad side behavior k v D x then varyingCycleFamilyWeight side k F x else 0) =
      ∑ x : CollisionAssignment n A B side k,
        if (∃ p q : CollisionSlot k, p ≠ q ∧ collisionNearby D p q x) ∨
            ∃ p, cycleEdgeNonmoderate side behavior k v p x then varyingCycleFamilyWeight side k F x else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : coreFamilyBad side behavior k v D x
    · exact (if_pos h).trans (if_pos h).symm
    · exact (if_neg h).trans (if_neg h).symm
  rw [hchange]
  exact hh.trans (add_le_add hcol hmod)

end Luce.Section6
