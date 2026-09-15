import Luce.Section6CollisionDefinitions
import Luce.Section5LowCycleRows

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem collisionCycleWeight_nonneg {α : Type*} {F : α → α → ℝ}
    (hF : ∀ a b, 0 ≤ F a b) (k : ℕ) (x : Fin (k+1) → α) :
    0 ≤ collisionCycleWeight F k x := Finset.prod_nonneg (fun _ _ => hF _ _)

theorem collisionCycleWeight_cons {α : Type*} (F : α → α → ℝ)
    (k : ℕ) (a : α) (x : Fin k → α) :
    collisionCycleWeight F k (Fin.cons a x) =
      forwardPathWeight F a x * F ((Fin.cons a x : Fin (k+1) → α) (Fin.last k)) a := by
  unfold collisionCycleWeight
  have he (j : Fin (k+1)) : (Fin.cons a x : Fin (k+1) → α) (finRotate (k+1) j) =
      (Fin.snoc x a : Fin (k+1) → α) j := congrFun (Fin.snoc_eq_cons_rotate x a).symm j
  simp_rw [he]
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, forwardPathWeight]

theorem collisionCycleWeight_rotate {α : Type*} (F : α → α → ℝ)
    (k : ℕ) (i : Fin (k+1)) (x : Fin (k+1) → α) :
    collisionCycleWeight F k (fun j => x (finCycle i j)) = collisionCycleWeight F k x := by
  unfold collisionCycleWeight
  have hcomm (j : Fin (k+1)) : finCycle i (finRotate (k+1) j) =
      finRotate (k+1) (finCycle i j) := by simp [finCycle_apply, add_right_comm]
  simp_rw [hcomm]
  exact Equiv.prod_comp (finCycle i) (fun j => F (x j) (x (finRotate (k+1) j)))

/-- A row bound propagates a terminal target bound to a marked interior
slot of an open path. The test function can depend on another fixed label. -/
theorem collision_path_test_bound {α : Type*} [Fintype α]
    (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b)
    (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b, F a b ≤ C) (htarget : ∀ a b, F a b ≤ C*v b)
    (k : ℕ) (i : Fin k) (a : α) (g : α → ℝ) (hg : ∀ b, 0 ≤ g b) :
    (∑ x : Fin k → α, forwardPathWeight F a x * g (x i)) ≤
      C^k * ∑ b, v b*g b := by
  induction k generalizing a with
  | zero => exact i.elim0
  | succ k ih =>
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => α))
      (fun ax : α × (Fin k → α) => forwardPathWeight F a (Fin.cons ax.1 ax.2)*
        g ((Fin.cons ax.1 ax.2 : Fin (k+1) → α) i)) _ (fun _ => rfl)]
    simp only [Fintype.sum_prod_type, forwardPathWeight_cons]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      calc
        _ = ∑ b, (F a b*g b)*(∑ x : Fin k → α, forwardPathWeight F b x) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro x _; ring
        _ ≤ ∑ b, (C*v b*g b)*C^k := Finset.sum_le_sum (fun b _ =>
          mul_le_mul (mul_le_mul_of_nonneg_right (htarget a b) (hg b))
            (forwardPathWeight_sum_le F hF C hC hrow k b)
            (Finset.sum_nonneg (fun x _ => Finset.prod_nonneg (fun j _ => hF _ _)))
            (mul_nonneg (mul_nonneg hC (hv b)) (hg b)))
        _ = _ := by
          rw [pow_succ', Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring
    · simp only [Fin.cons_succ]
      calc
        _ = ∑ b, F a b*(∑ x : Fin k → α, forwardPathWeight F b x*g (x j)) := by
          simp only [Finset.mul_sum, mul_assoc]
        _ ≤ ∑ b, F a b*(C^k*∑ z, v z*g z) :=
          Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (ih j b) (hF a b))
        _ = (∑ b, F a b)*(C^k*∑ z, v z*g z) := (Finset.sum_mul _ _ _).symm
        _ ≤ C*(C^k*∑ z, v z*g z) := mul_le_mul_of_nonneg_right (hrow a)
          (mul_nonneg (pow_nonneg hC _) (Finset.sum_nonneg (fun z _ => mul_nonneg (hv z) (hg z))))
        _ = _ := by rw [pow_succ']; ring

end Luce.Section6
