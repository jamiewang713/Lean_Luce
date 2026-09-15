import Luce.Section6CollisionPaths

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem collision_cycle_test_reindex {α : Type*} [Fintype α]
    (F : α → α → ℝ) (k : ℕ) (i : Fin (k+1))
    (g : (Fin (k+1) → α) → ℝ) :
    (∑ x, collisionCycleWeight F k x*g x) =
      ∑ x, collisionCycleWeight F k x*g (fun j => x ((finCycle i).symm j)) := by
  let e : (Fin (k+1) → α) ≃ (Fin (k+1) → α) :=
    { toFun := fun x j => x (finCycle i j)
      invFun := fun x j => x ((finCycle i).symm j)
      left_inv := by intro x; funext j; simp
      right_inv := by intro x; funext j; simp }
  apply Fintype.sum_equiv e
  intro x
  dsimp [e]
  rw [collisionCycleWeight_rotate]
  simp

theorem collision_cycle_test_zero_bound {α : Type*} [Fintype α]
    (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b)
    (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b, F a b ≤ C) (htarget : ∀ a b, F a b ≤ C*v b)
    (k : ℕ) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    (∑ x, collisionCycleWeight F k x*g (x 0)) ≤ C^(k+1)*∑ a, v a*g a := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => α))
    (fun ax : α × (Fin k → α) => collisionCycleWeight F k (Fin.cons ax.1 ax.2)*g ax.1)
    _ (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, collisionCycleWeight_cons]
  calc
    _ ≤ ∑ a, ∑ x : Fin k → α, forwardPathWeight F a x*(C*v a)*g a := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro x _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (htarget _ a)
        (Finset.prod_nonneg (fun j _ => hF _ _))) (hg a)
    _ = ∑ a, (C*v a*g a)*(∑ x : Fin k → α, forwardPathWeight F a x) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro x _; ring
    _ ≤ ∑ a, (C*v a*g a)*C^k := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (forwardPathWeight_sum_le F hF C hC hrow k a)
        (mul_nonneg (mul_nonneg hC (hv a)) (hg a)))
    _ = _ := by
      rw [pow_succ', Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _; ring

theorem collision_cycle_test_bound {α : Type*} [Fintype α]
    (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b)
    (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b, F a b ≤ C) (htarget : ∀ a b, F a b ≤ C*v b)
    (k : ℕ) (i : Fin (k+1)) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    (∑ x, collisionCycleWeight F k x*g (x i)) ≤ C^(k+1)*∑ a, v a*g a := by
  rw [collision_cycle_test_reindex F k i]
  simpa using collision_cycle_test_zero_bound F hF v hv hC hrow htarget k g hg

theorem collision_cycle_two_test_zero_bound {α : Type*} [Fintype α]
    (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b)
    (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b, F a b ≤ C) (htarget : ∀ a b, F a b ≤ C*v b)
    (k : ℕ) (j : Fin k) (g : α → α → ℝ) (hg : ∀ a b, 0 ≤ g a b) :
    (∑ x, collisionCycleWeight F k x*g (x 0) (x j.succ)) ≤
      C^(k+1)*∑ a, ∑ b, v a*v b*g a b := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => α))
    (fun ax : α × (Fin k → α) => collisionCycleWeight F k (Fin.cons ax.1 ax.2)*g ax.1 (ax.2 j))
    _ (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, collisionCycleWeight_cons]
  calc
    _ ≤ ∑ a, ∑ x : Fin k → α, (C*v a)*(forwardPathWeight F a x*g a (x j)) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro x _
      have hx : 0 ≤ forwardPathWeight F a x := Finset.prod_nonneg (fun j _ => hF _ _)
      convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (htarget _ a)
        hx) (hg a (x j)) using 1 <;> ring
    _ = ∑ a, (C*v a)*(∑ x : Fin k → α, forwardPathWeight F a x*g a (x j)) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ a, (C*v a)*(C^k*∑ b, v b*g a b) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
        (collision_path_test_bound F hF v hv hC hrow htarget k j a (g a) (hg a)) (mul_nonneg hC (hv a)))
    _ = _ := by
      rw [pow_succ']; simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _; ring

theorem collision_cycle_two_test_bound {α : Type*} [Fintype α]
    (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b)
    (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b, F a b ≤ C) (htarget : ∀ a b, F a b ≤ C*v b)
    (k : ℕ) (i j : Fin (k+1)) (hij : i ≠ j)
    (g : α → α → ℝ) (hg : ∀ a b, 0 ≤ g a b) :
    (∑ x, collisionCycleWeight F k x*g (x i) (x j)) ≤
      C^(k+1)*∑ a, ∑ b, v a*v b*g a b := by
  rw [collision_cycle_test_reindex F k i]
  have hi : (finCycle i).symm i = 0 := by apply (finCycle i).injective; simp
  have hj : (finCycle i).symm j ≠ 0 := by
    intro h
    have := congrArg (finCycle i) h
    simp at this
    exact hij this.symm
  simp only [hi]
  obtain ⟨j', hj'⟩ := Fin.exists_succ_eq.mpr hj
  rw [← hj']
  exact collision_cycle_two_test_zero_bound F hF v hv hC hrow htarget k j' g hg

end Luce.Section6
