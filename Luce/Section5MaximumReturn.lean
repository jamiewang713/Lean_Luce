import Luce.Section5MaximumCylinder
import Luce.Section5ShellMarkedEdge

noncomputable section
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Drop only the internal distinctness and retention restrictions. The
marked predecessor u remains retained and strictly below the maximum v. -/
theorem retained_maximum_ghost_sum_le_return {n : ℕ} (w : Weights n)
    (k : ℕ) (S : Finset (Fin n)) (old : Fin n → ℝ) (v : Fin n) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin (k+1) → Fin n =>
      Function.Injective u ∧ (∀ a, u a < v) ∧
        ∀ a, (Fin.cons v u : Fin (k+2) → Fin n) a ∈ S),
      ∏ a : Fin (k+2), ghostEntry w (k+2) old
        ((Fin.cons v u : Fin (k+2) → Fin n) a)
        ((Fin.snoc u v : Fin (k+2) → Fin n) a)) ≤
      ∑ u : Fin n, if u ∈ S ∧ u < v then
        ghostEntry w (k+2) old u v * markedReturnWeight (ghostEntry w (k+2) old) k v u else 0 := by
  classical
  let p := ghostEntry w (k+2) old
  have hp (i j : Fin n) : 0 ≤ p i j := (ghostEntry_mem_Icc w (k+2) old i j).1
  simp_rw [rootedGhostProduct_eq_forward, Fin.cons_last]
  apply le_trans (b := ∑ u : Fin (k+1) → Fin n,
    if u (Fin.last k) ∈ S ∧ u (Fin.last k) < v then
      forwardPathWeight p v u * p (u (Fin.last k)) v else 0)
  · rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro u _
    split_ifs with hu hlast
    · exact le_rfl
    · exact False.elim (hlast ⟨by simpa only [Fin.cons_last] using hu.2.2 (Fin.last (k+1)),
        hu.2.1 (Fin.last k)⟩)
    · exact mul_nonneg (Finset.prod_nonneg (fun _ _ => hp _ _)) (hp _ _)
    · exact le_rfl
  · have heq : (∑ u : Fin (k+1) → Fin n,
        if u (Fin.last k) ∈ S ∧ u (Fin.last k) < v then
          forwardPathWeight p v u * p (u (Fin.last k)) v else 0) =
        ∑ xu : Fin n × (Fin k → Fin n), if xu.1 ∈ S ∧ xu.1 < v then
          forwardPathWeight p v (Fin.snoc xu.2 xu.1) * p xu.1 v else 0 := by
      symm
      apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (k+1) => Fin n))
      intro xu
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last]
    rw [heq, Fintype.sum_prod_type]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : u ∈ S ∧ u < v
    · simp only [if_pos hu, markedReturnWeight, mul_comm]
      rw [← Finset.mul_sum]
    · simp only [if_neg hu, Finset.sum_const_zero]

end Luce
