import Luce.Section6CollisionVaryingMatrices
import Luce.Section6FiniteBadSetSum

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

def varyingCycleFamilyWeight {s n A B : ℕ} (side : Fin s → Corner) (k : Fin s → ℕ)
    (F : Fin s → Fin n → Fin n → ℝ) (x : CollisionAssignment n A B side k) : ℝ :=
  ∏ c, collisionCycleWeight (fun a b => F c a.val b.val) (k c) (x c)

theorem varying_cycle_family_nonneg {s n A B : ℕ} (side : Fin s → Corner) (k : Fin s → ℕ)
    (F : Fin s → Fin n → Fin n → ℝ) (hF : ∀ c a b, 0 ≤ F c a b)
    (x : CollisionAssignment n A B side k) : 0 ≤ varyingCycleFamilyWeight side k F x :=
  Finset.prod_nonneg (fun c _ => collisionCycleWeight_nonneg
    (fun a b : CollisionCore n A B (side c) => hF c a.val b.val) (k c) (x c))

theorem cycle_family_single_test_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (w : ∀ i, β i → ℝ) (hw : ∀ i x, 0 ≤ w i x)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (htrace : ∀ i, ∑ x, w i x ≤ T)
    (i : ι) (g : β i → ℝ) (htest : ∑ x, w i x*g x ≤ R) :
    (∑ x : ∀ i, β i, (∏ c, w c (x c))*g (x i)) ≤ R*T^(Fintype.card ι-1) := by
  rw [collision_product_test_one w i g]
  exact mul_le_mul htest (collision_complement_product_le i (fun c => ∑ x, w c x)
    (fun c => Finset.sum_nonneg (fun x _ => hw c x)) hT htrace)
    (Finset.prod_nonneg (fun c _ => Finset.sum_nonneg (fun x _ => hw c.val x))) hR

theorem varying_cycle_family_sum_bound {s n A B L : ℕ}
    (hA : 1 ≤ A) (hAB : A ≤ B) (side : Fin s → Corner) (k : Fin s → ℕ)
    (hk : ∀ c, k c+1 ≤ L) (F : Fin s → Fin n → Fin n → ℝ)
    (hF : ∀ c a b, 0 ≤ F c a b) {C : ℝ} (hC : 1 ≤ C)
    (hrow : ∀ c a, ∑ b, F c a b ≤ C)
    (htarget : ∀ c (b : CollisionCore n A B (side c)) a,
      F c a b.val ≤ C/(cornerDistance (side c) b.val : ℝ)) :
    (∑ x : CollisionAssignment n A B side k, varyingCycleFamilyWeight side k F x) ≤
      (C^L*(1+Real.log ((B : ℝ)/A)))^s := by
  unfold varyingCycleFamilyWeight
  rw [← Fintype.prod_sum]
  calc
    _ ≤ ∏ _c : Fin s, C^L*(1+Real.log ((B : ℝ)/A)) := by
      apply Finset.prod_le_prod
      · intro c _
        exact Finset.sum_nonneg (fun x _ => collisionCycleWeight_nonneg
          (fun a b : CollisionCore n A B (side c) => hF c a.val b.val) (k c) x)
      · intro c _
        exact collision_core_cycle_trace (side c) hA hAB (F c) (hF c) hC (hrow c) (htarget c) (hk c)
    _ = _ := by simp

theorem varying_cycle_family_collision_bound {s n A B L : ℕ} (D : ℕ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (side : Fin s → Corner) (k : Fin s → ℕ)
    (hk : ∀ c, k c+1 ≤ L) (F : Fin s → Fin n → Fin n → ℝ)
    (hF : ∀ c a b, 0 ≤ F c a b) {C : ℝ} (hC : 1 ≤ C)
    (hrow : ∀ c a, ∑ b, F c a b ≤ C)
    (htarget : ∀ c (b : CollisionCore n A B (side c)) a,
      F c a b.val ≤ C/(cornerDistance (side c) b.val : ℝ)) :
    collisionUnionSum (varyingCycleFamilyWeight (A := A) (B := B) side k F) D ≤
      (s*L : ℕ)^2*(C^L)^2*(2*(2*(D : ℝ)+1)/(A : ℝ))*
        (C^L*(1+Real.log ((B : ℝ)/A)))^(s-1) := by
  have ha : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hH : 0 ≤ 1+Real.log ((B : ℝ)/A) := by
    have hh := Real.log_nonneg ((one_le_div ha).mpr (show (A : ℝ) ≤ B by exact_mod_cast hAB))
    linarith
  have hR : 0 ≤ (C^L)^2*(2*(2*(D : ℝ)+1)/(A : ℝ))*
      (C^L*(1+Real.log ((B : ℝ)/A)))^(s-1) := by positivity
  have hh := collision_union_le_card_sq (varyingCycleFamilyWeight (A := A) (B := B) side k F)
    (varying_cycle_family_nonneg side k F hF) D hR
    (collision_varying_matrices_pair_bound D hA hAB side k hk F hF hC hrow htarget)
  have hc : (Fintype.card (CollisionSlot k) : ℝ) ≤ (s*L : ℕ) := by
    exact_mod_cast collision_slot_card_le k hk
  have hc0 : (0 : ℝ) ≤ Fintype.card (CollisionSlot k) := Nat.cast_nonneg _
  have hs : (Fintype.card (CollisionSlot k) : ℝ)^2 ≤ ((s*L : ℕ) : ℝ)^2 := by nlinarith
  exact hh.trans ((mul_le_mul_of_nonneg_right hs hR).trans_eq (by ring))

end Luce.Section6
