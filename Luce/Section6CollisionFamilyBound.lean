import Luce.Section6CollisionCoreTests
import Luce.Section6CollisionProductSums

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem collision_pair_sum_test {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    (W : CollisionAssignment n A B side k → ℝ) (D : ℕ) (p q : CollisionSlot k) :
    collisionPairSum W D p q = ∑ x, W x *
      (if Nat.dist (collisionLabel x p).val (collisionLabel x q).val ≤ D then 1 else 0) := by
  classical
  unfold collisionPairSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : collisionNearby D p q x
  · have h' : Nat.dist (collisionLabel x p).val (collisionLabel x q).val ≤ D := h
    rw [if_pos h, if_pos h', mul_one]
  · have h' : ¬ Nat.dist (collisionLabel x p).val (collisionLabel x q).val ≤ D := h
    rw [if_neg h, if_neg h', mul_zero]

theorem collision_family_pair_bound {s n A B L : ℕ} (D : ℕ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (side : Fin s → Corner) (k : Fin s → ℕ)
    (hk : ∀ c, k c+1 ≤ L) (F : Fin n → Fin n → ℝ)
    (hF : ∀ a b, 0 ≤ F a b) {C : ℝ} (hC : 1 ≤ C)
    (hrow : ∀ a, ∑ b, F a b ≤ C)
    (htarget : ∀ c (b : CollisionCore n A B (side c)) a,
      F a b.val ≤ C/(cornerDistance (side c) b.val : ℝ))
    (p q : CollisionSlot k) (hpq : p ≠ q) :
    collisionPairSum (collisionFamilyWeight (A := A) (B := B) side k F) D p q ≤
      (C^L)^2*(2*(2*(D : ℝ)+1)/(A : ℝ))*(C^L*(1+Real.log ((B : ℝ)/A)))^(s-1) := by
  classical
  let Q := C^L
  let H := 1+Real.log ((B : ℝ)/A)
  let R := 2*(2*(D : ℝ)+1)/(A : ℝ)
  let T := Q*H
  let w (c : Fin s) (x : Fin (k c+1) → CollisionCore n A B (side c)) :=
    collisionCycleWeight (fun a b => F a.val b.val) (k c) x
  let v (c : Fin s) (a : CollisionCore n A B (side c)) := 1/(cornerDistance (side c) a.val : ℝ)
  have hQ : 1 ≤ Q := one_le_pow₀ hC
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hH : 1 ≤ H := by
    have ha : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
    have hh : 0 ≤ Real.log ((B : ℝ)/A) := Real.log_nonneg ((one_le_div ha).mpr (by exact_mod_cast hAB))
    dsimp [H]; linarith
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hQ hH
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hw (c : Fin s) (x : Fin (k c+1) → CollisionCore n A B (side c)) : 0 ≤ w c x :=
    collisionCycleWeight_nonneg (fun a b : CollisionCore n A B (side c) => hF a.val b.val) _ _
  have hv (c : Fin s) (a : CollisionCore n A B (side c)) : 0 ≤ v c a := by dsimp [v]; positivity
  have htrace (c : Fin s) : (∑ x, w c x) ≤ T :=
    collision_core_cycle_trace (side c) hA hAB F hF hC hrow (htarget c) (hk c)
  have hnear (c d : Fin s) :
      (∑ a : CollisionCore n A B (side c), ∑ b : CollisionCore n A B (side d),
        v c a*v d b*(if Nat.dist a.val.val b.val.val ≤ D then 1 else 0)) ≤ R := by
    simpa only [v, R, mul_ite, mul_one, mul_zero] using
      collision_nearby_reciprocal_sum (side c) (side d) hA hAB D
  rcases p with ⟨i, p⟩
  rcases q with ⟨j, q⟩
  by_cases hij : i = j
  · subst j
    have hpq' : p ≠ q := by intro h; subst q; exact hpq rfl
    let g (x : Fin (k i+1) → CollisionCore n A B (side i)) : ℝ :=
      if Nat.dist (x p).val.val (x q).val.val ≤ D then 1 else 0
    have hblock : (∑ x, w i x*g x) ≤ Q^2*R := by
      have hh := collision_core_cycle_two_test (side i) F hF hC hrow (htarget i) (hk i) p q hpq'
        (fun a b => if Nat.dist a.val.val b.val.val ≤ D then 1 else 0) (fun _ _ => by positivity)
      have hq2 : Q ≤ Q^2 := by nlinarith only [hQ]
      exact (hh.trans (mul_le_mul_of_nonneg_left (hnear i i) hQ0)).trans
        (mul_le_mul_of_nonneg_right hq2 hR)
    have hrest := collision_complement_product_le i (fun c => ∑ x, w c x)
      (fun c => Finset.sum_nonneg (fun x _ => hw c x)) (zero_le_one.trans hT) htrace
    simp only [Fintype.card_fin] at hrest
    have hb : (∑ x : CollisionAssignment n A B side k, (∏ c, w c (x c))*g (x i)) ≤
        Q^2*R*T^(s-1) := by
      rw [collision_product_test_one w i g]
      exact mul_le_mul hblock hrest
        (Finset.prod_nonneg (fun c _ => Finset.sum_nonneg (fun x _ => hw c.val x)))
        (mul_nonneg (sq_nonneg _) hR)
    rw [collision_pair_sum_test]
    exact hb
  · let g (x : Fin (k i+1) → CollisionCore n A B (side i))
        (y : Fin (k j+1) → CollisionCore n A B (side j)) : ℝ :=
      if Nat.dist (x p).val.val (y q).val.val ≤ D then 1 else 0
    have hblock : (∑ x, ∑ y, w i x*w j y*g x y) ≤ Q^2*R := by
      have hh := collision_two_test_tensor (w i) (w j) (hw i) (hw j)
        (fun x => x p) (fun y => y q) (v i) (v j) (hv i) (hv j) hQ0
        (fun f hf => collision_core_cycle_test (side i) F hF hC hrow (htarget i) (hk i) p f hf)
        (fun f hf => collision_core_cycle_test (side j) F hF hC hrow (htarget j) (hk j) q f hf)
        (fun a b => if Nat.dist a.val.val b.val.val ≤ D then 1 else 0) (fun _ _ => by positivity)
      exact hh.trans (mul_le_mul_of_nonneg_left (hnear i j) (sq_nonneg _))
    have hrest := collision_two_complement_product_le i j (Ne.symm hij) (fun c => ∑ x, w c x)
      (fun c => Finset.sum_nonneg (fun x _ => hw c x)) hT htrace
    simp only [Fintype.card_fin] at hrest
    have hb : (∑ x : CollisionAssignment n A B side k, (∏ c, w c (x c))*g (x i) (x j)) ≤
        Q^2*R*T^(s-1) := by
      rw [collision_product_test_two w i j (Ne.symm hij) g]
      exact mul_le_mul hblock hrest
        (Finset.prod_nonneg (fun c _ => Finset.sum_nonneg (fun x _ => hw c.val.val x)))
        (mul_nonneg (sq_nonneg _) hR)
    rw [collision_pair_sum_test]
    exact hb

end Luce.Section6
