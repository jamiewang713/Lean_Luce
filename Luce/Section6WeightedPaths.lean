import Luce.Section5LowCycleRows

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- A weighted row estimate propagates along paths, controlling the sum
of the potentials at all visited vertices, not just the final vertex. -/
theorem forward_path_occupation_bound {α : Type*} [Fintype α]
    (p : α → α → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (V : α → ℝ) (hV : ∀ i, 0 ≤ V i)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, p i j ≤ C)
    (hweighted : ∀ i, ∑ j, p i j * V j ≤ C * V i)
    (k : ℕ) (v : α) :
    (∑ u : Fin k → α, forwardPathWeight p v u * ∑ a, V (u a))
      ≤ (k : ℝ) * C^k * V v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    have he : (∑ u : Fin (k+1) → α, forwardPathWeight p v u * ∑ a, V (u a)) =
        ∑ x, p v x * (V x * (∑ u : Fin k → α, forwardPathWeight p x u) +
          ∑ u : Fin k → α, forwardPathWeight p x u * ∑ a, V (u a)) := by
      rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => α))
        (fun xu : α × (Fin k → α) => forwardPathWeight p v (Fin.cons xu.1 xu.2) *
          ∑ a, V ((Fin.cons xu.1 xu.2 : Fin (k+1) → α) a))
        (fun u => forwardPathWeight p v u * ∑ a, V (u a)) (fun _ => rfl)]
      simp only [Fintype.sum_prod_type, forwardPathWeight_cons, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx <;>
        apply Finset.sum_congr rfl <;> intro u hu <;> ring
    rw [he]
    calc
      _ ≤ ∑ x, p v x * (V x * C^k + (k : ℝ)*C^k*V x) := by
        apply Finset.sum_le_sum
        intro x hx
        apply mul_le_mul_of_nonneg_left _ (hp v x)
        exact add_le_add (mul_le_mul_of_nonneg_left
          (forwardPathWeight_sum_le p hp C hC hrow k x) (hV x)) (ih x)
      _ = ((k : ℝ)+1)*C^k * ∑ x, p v x * V x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ ≤ ((k : ℝ)+1)*C^k * (C*V v) :=
        mul_le_mul_of_nonneg_left (hweighted v) (by positivity)
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, pow_succ]; ring

/-- Paths which visit a vertex with potential at least L are controlled
by the occupation estimate. No first-hitting or independence premise is used. -/
theorem forward_path_escape_bound {α : Type*} [Fintype α]
    (p : α → α → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (V : α → ℝ) (hV : ∀ i, 0 ≤ V i)
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hrow : ∀ i, ∑ j, p i j ≤ C)
    (hweighted : ∀ i, ∑ j, p i j * V j ≤ C * V i)
    (k : ℕ) (v : α) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin k → α => ∃ a, L ≤ V (u a)),
      forwardPathWeight p v u) ≤ (k : ℝ)*C^k*V v/L := by
  classical
  apply (le_div_iff₀ hL).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ u ∈ Finset.univ.filter (fun u : Fin k → α => ∃ a, L ≤ V (u a)),
        forwardPathWeight p v u * ∑ a, V (u a) := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hu).2
      apply mul_le_mul_of_nonneg_left
        (ha.trans (Finset.single_le_sum (fun b _ => hV (u b)) (Finset.mem_univ a)))
      exact Finset.prod_nonneg (fun b _ => hp _ _)
    _ ≤ ∑ u : Fin k → α, forwardPathWeight p v u * ∑ a, V (u a) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro u hu hnot
      exact mul_nonneg (Finset.prod_nonneg (fun b _ => hp _ _))
        (Finset.sum_nonneg (fun a _ => hV (u a)))
    _ ≤ _ := forward_path_occupation_bound p hp V hV hC hrow hweighted k v

end Luce.Section6
