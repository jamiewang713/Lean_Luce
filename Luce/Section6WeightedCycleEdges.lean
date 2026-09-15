import Luce.Section6CollisionCycleTests

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem forward_path_terminal_potential {α : Type*} [Fintype α]
    (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b) (V : α → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ a, ∑ b, F a b*V b ≤ C*V a)
    (k : ℕ) (a : α) :
    (∑ x : Fin k → α, forwardPathWeight F a x*
      V ((Fin.cons a x : Fin (k+1) → α) (Fin.last k))) ≤ C^k*V a := by
  induction k generalizing a with
  | zero => simp [forwardPathWeight]
  | succ k ih =>
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => α))
      (fun bx : α × (Fin k → α) => forwardPathWeight F a (Fin.cons bx.1 bx.2)*
        V ((Fin.cons bx.1 bx.2 : Fin (k+1) → α) (Fin.last k))) _ (fun _ => rfl)]
    simp only [Fintype.sum_prod_type, forwardPathWeight_cons]
    calc
      _ = ∑ b, F a b*(∑ x : Fin k → α, forwardPathWeight F b x*
          V ((Fin.cons b x : Fin (k+1) → α) (Fin.last k))) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ ≤ ∑ b, F a b*(C^k*V b) := Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_left (ih b) (hF a b))
      _ = C^k*∑ b, F a b*V b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b _; ring
      _ ≤ C^k*(C*V a) := mul_le_mul_of_nonneg_left (hw a) (pow_nonneg hC k)
      _ = _ := by rw [pow_succ]; ring

theorem cycle_closing_potential_bound {α : Type*} [Fintype α]
    (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b)
    (V : α → ℝ) (hV : ∀ a, 0 < V a) (v : α → ℝ) (hv : ∀ a, 0 ≤ v a)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ a, ∑ b, F a b*V b ≤ C*V a)
    (ht : ∀ a b, F a b ≤ C*v b) (k : ℕ) :
    (∑ x, collisionCycleWeight F k x*(V (x (Fin.last k))/V (x 0))) ≤
      C^(k+1)*∑ a, v a := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => α))
    (fun ax : α × (Fin k → α) => collisionCycleWeight F k (Fin.cons ax.1 ax.2)*
      (V ((Fin.cons ax.1 ax.2 : Fin (k+1) → α) (Fin.last k))/V ax.1)) _ (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, collisionCycleWeight_cons]
  calc
    _ ≤ ∑ a, ∑ x : Fin k → α, forwardPathWeight F a x*(C*v a)*
        (V ((Fin.cons a x : Fin (k+1) → α) (Fin.last k))/V a) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro x _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht _ a)
        (Finset.prod_nonneg (fun j _ => hF _ _))) (div_nonneg (hV _).le (hV _).le)
    _ = ∑ a, (C*v a/V a)*(∑ x : Fin k → α, forwardPathWeight F a x*
        V ((Fin.cons a x : Fin (k+1) → α) (Fin.last k))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro x _; ring
    _ ≤ ∑ a, (C*v a/V a)*(C^k*V a) := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (forward_path_terminal_potential F hF V hC hw k a)
        (div_nonneg (mul_nonneg hC (hv a)) (hV a).le))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      field_simp [(hV a).ne']
      <;> ring

theorem cycle_edge_potential_bound {α : Type*} [Fintype α]
    (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b)
    (V : α → ℝ) (hV : ∀ a, 0 < V a) (v : α → ℝ) (hv : ∀ a, 0 ≤ v a)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ a, ∑ b, F a b*V b ≤ C*V a)
    (ht : ∀ a b, F a b ≤ C*v b) (k : ℕ) (i : Fin (k+1)) :
    (∑ x, collisionCycleWeight F k x*(V (x i)/V (x (finRotate (k+1) i)))) ≤
      C^(k+1)*∑ a, v a := by
  rw [collision_cycle_test_reindex F k (finRotate (k+1) i)]
  have hs : (finCycle (finRotate (k+1) i)).symm i = Fin.last k := by
    apply (finCycle (finRotate (k+1) i)).symm_apply_eq.mpr
    simp only [finCycle_apply, finRotate_apply]
    symm
    calc
      Fin.last k+(i+1) = (Fin.last k+1)+i := by abel
      _ = i := by rw [← finRotate_apply, finRotate_last, zero_add]
  have ht0 : (finCycle (finRotate (k+1) i)).symm (finRotate (k+1) i) = 0 := by
    simp [finCycle_symm_apply]
  simp_rw [hs, ht0]
  exact cycle_closing_potential_bound F hF V hV v hv hC hw ht k

/-- Markov's inequality for a large ratio across any fixed directed edge.
The cycle may repeat vertices; every restriction may subsequently be dropped. -/
theorem cycle_large_edge_potential_bound {α : Type*} [Fintype α]
    (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b)
    (V : α → ℝ) (hV : ∀ a, 0 < V a) (v : α → ℝ) (hv : ∀ a, 0 ≤ v a)
    {C Q : ℝ} (hC : 0 ≤ C) (hQ : 0 < Q)
    (hw : ∀ a, ∑ b, F a b*V b ≤ C*V a)
    (ht : ∀ a b, F a b ≤ C*v b) (k : ℕ) (i : Fin (k+1)) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin (k+1) → α =>
      Q ≤ V (x i)/V (x (finRotate (k+1) i))), collisionCycleWeight F k x) ≤
      (C^(k+1)*∑ a, v a)/Q := by
  apply (le_div_iff₀ hQ).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin (k+1) → α =>
        Q ≤ V (x i)/V (x (finRotate (k+1) i))),
        collisionCycleWeight F k x*(V (x i)/V (x (finRotate (k+1) i))) := by
      apply Finset.sum_le_sum; intro x hx
      exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 (collisionCycleWeight_nonneg hF k x)
    _ ≤ ∑ x, collisionCycleWeight F k x*(V (x i)/V (x (finRotate (k+1) i))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro x _ _
      exact mul_nonneg (collisionCycleWeight_nonneg hF k x) (div_nonneg (hV _).le (hV _).le)
    _ ≤ _ := cycle_edge_potential_bound F hF V hV v hv hC hw ht k i

end Luce.Section6
