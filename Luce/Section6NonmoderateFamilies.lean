import Luce.Section6FactorialFamilyBounds
import Luce.Section6NonmoderateCycles

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

def cycleEdgeNonmoderate {s n A B : ℕ} (side : Fin s → Corner)
    (behavior : Fin s → EndpointBehavior) (k : Fin s → ℕ) (v : ℝ)
    (p : CollisionSlot k) (x : CollisionAssignment n A B side k) : Prop :=
  ¬ localCornerRatio (side p.1) (behavior p.1)
    (cornerDistance (side p.1) (x p.1 p.2).val)
    (cornerDistance (side p.1) (x p.1 (finRotate (k p.1+1) p.2)).val) ≤
      (min (cornerDistance (side p.1) (x p.1 p.2).val : ℝ)
        (cornerDistance (side p.1) (x p.1 (finRotate (k p.1+1) p.2)).val : ℝ))^v

theorem nonmoderate_cycle_family_sum {s n A B L : ℕ}
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
      if ∃ p, cycleEdgeNonmoderate side behavior k v p x then varyingCycleFamilyWeight side k F x else 0) ≤
      (s*L : ℕ)*((C^L*(1+Real.log ((B : ℝ)/A)))/(A : ℝ)^eta)*
        (C^L*(1+Real.log ((B : ℝ)/A)))^(s-1) := by
  classical
  let T := C^L*(1+Real.log ((B : ℝ)/A))
  let R := T/(A : ℝ)^eta
  let w (c : Fin s) (x : Fin (k c+1) → CollisionCore n A B (side c)) :=
    collisionCycleWeight (fun a b => F c a.val b.val) (k c) x
  have ha : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hH : 0 ≤ 1+Real.log ((B : ℝ)/A) := by
    have hh := Real.log_nonneg ((one_le_div ha).mpr (show (A : ℝ) ≤ B by exact_mod_cast hAB))
    linarith
  have hT : 0 ≤ T := mul_nonneg (pow_nonneg (zero_le_one.trans hC) L) hH
  have hR : 0 ≤ R := div_nonneg hT (Real.rpow_nonneg ha.le eta)
  have hw0 (c : Fin s) (x : Fin (k c+1) → CollisionCore n A B (side c)) : 0 ≤ w c x :=
    collisionCycleWeight_nonneg (fun a b : CollisionCore n A B (side c) => hF c a.val b.val) (k c) x
  have htrace (c : Fin s) : (∑ x, w c x) ≤ T :=
    collision_core_cycle_trace (side c) hA hAB (F c) (hF c) hC (hrow c) (htarget c) (hk c)
  have hedge (p : CollisionSlot k) :
      (∑ x : CollisionAssignment n A B side k,
        if cycleEdgeNonmoderate side behavior k v p x then varyingCycleFamilyWeight side k F x else 0) ≤
      R*T^(s-1) := by
    obtain ⟨c, i⟩ := p
    let g (x : Fin (k c+1) → CollisionCore n A B (side c)) : ℝ :=
      if ¬ localCornerRatio (side c) (behavior c)
        (cornerDistance (side c) (x i).val) (cornerDistance (side c) (x (finRotate (k c+1) i)).val) ≤
          (min (cornerDistance (side c) (x i).val : ℝ)
            (cornerDistance (side c) (x (finRotate (k c+1) i)).val : ℝ))^v then 1 else 0
    have htest : (∑ x, w c x*g x) ≤ R := by
      have hh := nonmoderate_cycle_edge_sum (side c) (behavior c) hA hAB (F c) (hF c)
        hC hv (hkap c) (hg c) (heta c) (hk c) (hw c) (htarget c) i
      simpa only [Finset.sum_filter, w, g, mul_ite, mul_one, mul_zero] using hh
    have hh := cycle_family_single_test_bound w hw0 hT hR htrace c g htest
    have he : (∑ x : CollisionAssignment n A B side k,
        if cycleEdgeNonmoderate side behavior k v ⟨c, i⟩ x then varyingCycleFamilyWeight side k F x else 0) =
        ∑ x : CollisionAssignment n A B side k, (∏ d, w d (x d))*g (x c) := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [cycleEdgeNonmoderate, varyingCycleFamilyWeight, g, w]
      rw [mul_ite, mul_one, mul_zero]
      by_cases h : cycleEdgeNonmoderate side behavior k v ⟨c, i⟩ x
      · exact (if_pos h).trans (if_pos h).symm
      · exact (if_neg h).trans (if_neg h).symm
    rw [he]
    simpa only [Fintype.card_fin] using hh
  have hc : (Fintype.card (CollisionSlot k) : ℝ) ≤ (s*L : ℕ) := by
    exact_mod_cast collision_slot_card_le k hk
  calc
    _ ≤ ∑ p : CollisionSlot k, ∑ x : CollisionAssignment n A B side k,
        if cycleEdgeNonmoderate side behavior k v p x then varyingCycleFamilyWeight side k F x else 0 :=
      finite_union_weight_sum _ (varying_cycle_family_nonneg side k F hF) _
    _ ≤ ∑ _p : CollisionSlot k, R*T^(s-1) := Finset.sum_le_sum (fun p _ => hedge p)
    _ = (Fintype.card (CollisionSlot k) : ℝ)*(R*T^(s-1)) := by simp
    _ ≤ (s*L : ℕ)*(R*T^(s-1)) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hR (pow_nonneg hT _))
    _ = _ := by dsimp [R, T]; ring

end Luce.Section6
