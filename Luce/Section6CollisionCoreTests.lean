import Luce.Section6CollisionCycleTests
import Luce.Section6CollisionDepthSums

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem collision_core_matrix_row {n A B : ℕ} (side : Corner)
    (F : Fin n → Fin n → ℝ) (hF : ∀ a b, 0 ≤ F a b) {C : ℝ}
    (hrow : ∀ a, ∑ b, F a b ≤ C) (a : CollisionCore n A B side) :
    (∑ b : CollisionCore n A B side, F a.val b.val) ≤ C := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image (Subtype.val : CollisionCore n A B side → Fin n), F a.val b :=
      (Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)).symm
    _ ≤ ∑ b : Fin n, F a.val b := Finset.sum_le_univ_sum_of_nonneg (hF a.val)
    _ ≤ _ := hrow a.val

theorem collision_core_cycle_test {n A B k L : ℕ} (side : Corner)
    (F : Fin n → Fin n → ℝ) (hF : ∀ a b, 0 ≤ F a b) {C : ℝ} (hC : 1 ≤ C)
    (hrow : ∀ a, ∑ b, F a b ≤ C)
    (htarget : ∀ (b : CollisionCore n A B side) a,
      F a b.val ≤ C/(cornerDistance side b.val : ℝ)) (hk : k+1 ≤ L)
    (i : Fin (k+1)) (g : CollisionCore n A B side → ℝ) (hg : ∀ a, 0 ≤ g a) :
    (∑ x, collisionCycleWeight (fun a b => F a.val b.val) k x*g (x i)) ≤
      C^L*∑ a, (1/(cornerDistance side a.val : ℝ))*g a := by
  have hh := collision_cycle_test_bound (fun a b : CollisionCore n A B side => F a.val b.val)
    (fun a b => hF a.val b.val) (fun a => 1/(cornerDistance side a.val : ℝ))
    (fun _ => by positivity) (zero_le_one.trans hC) (collision_core_matrix_row side F hF hrow)
    (fun a b => by simpa [div_eq_mul_inv] using htarget b a.val) k i g hg
  exact hh.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hk)
    (Finset.sum_nonneg (fun a _ => mul_nonneg (by positivity) (hg a))))

theorem collision_core_cycle_two_test {n A B k L : ℕ} (side : Corner)
    (F : Fin n → Fin n → ℝ) (hF : ∀ a b, 0 ≤ F a b) {C : ℝ} (hC : 1 ≤ C)
    (hrow : ∀ a, ∑ b, F a b ≤ C)
    (htarget : ∀ (b : CollisionCore n A B side) a,
      F a b.val ≤ C/(cornerDistance side b.val : ℝ)) (hk : k+1 ≤ L)
    (i j : Fin (k+1)) (hij : i ≠ j)
    (g : CollisionCore n A B side → CollisionCore n A B side → ℝ) (hg : ∀ a b, 0 ≤ g a b) :
    (∑ x, collisionCycleWeight (fun a b => F a.val b.val) k x*g (x i) (x j)) ≤
      C^L*∑ a, ∑ b, (1/(cornerDistance side a.val : ℝ))*(1/(cornerDistance side b.val : ℝ))*g a b := by
  have hh := collision_cycle_two_test_bound (fun a b : CollisionCore n A B side => F a.val b.val)
    (fun a b => hF a.val b.val) (fun a => 1/(cornerDistance side a.val : ℝ))
    (fun _ => by positivity) (zero_le_one.trans hC) (collision_core_matrix_row side F hF hrow)
    (fun a b => by simpa [div_eq_mul_inv] using htarget b a.val) k i j hij g hg
  exact hh.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hk)
    (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      mul_nonneg (by positivity) (hg a b)))))

theorem collision_core_cycle_trace {n A B k L : ℕ} (side : Corner)
    (hA : 1 ≤ A) (hAB : A ≤ B)
    (F : Fin n → Fin n → ℝ) (hF : ∀ a b, 0 ≤ F a b) {C : ℝ} (hC : 1 ≤ C)
    (hrow : ∀ a, ∑ b, F a b ≤ C)
    (htarget : ∀ (b : CollisionCore n A B side) a,
      F a b.val ≤ C/(cornerDistance side b.val : ℝ)) (hk : k+1 ≤ L) :
    (∑ x : Fin (k+1) → CollisionCore n A B side,
      collisionCycleWeight (fun a b => F a.val b.val) k x) ≤ C^L*(1+Real.log ((B : ℝ)/A)) := by
  have hh := collision_core_cycle_test side F hF hC hrow htarget hk 0 (fun _ => 1) (fun _ => zero_le_one)
  simp only [mul_one] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (collision_core_harmonic side hA hAB)
    (pow_nonneg (zero_le_one.trans hC) _))

/-- Tensorization of two one-slot test inequalities. This is finite
summation, not an independence hypothesis on insertion factors. -/
theorem collision_two_test_tensor {α β X Y : Type*} [Fintype α] [Fintype β] [Fintype X] [Fintype Y]
    (w : X → ℝ) (z : Y → ℝ) (hw : ∀ x, 0 ≤ w x) (hz : ∀ y, 0 ≤ z y)
    (p : X → α) (q : Y → β) (u : α → ℝ) (v : β → ℝ)
    (hu : ∀ a, 0 ≤ u a) (hv : ∀ b, 0 ≤ v b) {Q : ℝ} (hQ : 0 ≤ Q)
    (hp : ∀ g : α → ℝ, (∀ a, 0 ≤ g a) → (∑ x, w x*g (p x)) ≤ Q*∑ a, u a*g a)
    (hq : ∀ g : β → ℝ, (∀ b, 0 ≤ g b) → (∑ y, z y*g (q y)) ≤ Q*∑ b, v b*g b)
    (g : α → β → ℝ) (hg : ∀ a b, 0 ≤ g a b) :
    (∑ x, ∑ y, w x*z y*g (p x) (q y)) ≤ Q^2*∑ a, ∑ b, u a*v b*g a b := by
  calc
    _ = ∑ x, w x*(∑ y, z y*g (p x) (q y)) := by simp only [Finset.mul_sum, mul_assoc]
    _ ≤ ∑ x, w x*(Q*∑ b, v b*g (p x) b) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hq (g (p x)) (hg (p x))) (hw x))
    _ = Q*(∑ x, w x*(∑ b, v b*g (p x) b)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro b _; ring
    _ ≤ Q*(Q*∑ a, u a*(∑ b, v b*g a b)) := mul_le_mul_of_nonneg_left
      (hp (fun a => ∑ b, v b*g a b) (fun a => Finset.sum_nonneg (fun b _ => mul_nonneg (hv b) (hg a b)))) hQ
    _ = _ := by simp only [Finset.mul_sum]; ring

end Luce.Section6
