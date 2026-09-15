import Luce.Section5LowCycleRows

noncomputable section
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Unrestricted return paths with k intermediate labels and fixed end u.
At k=0 this is the single edge from v to u. -/
def markedReturnWeight {α : Type*} [Fintype α] (p : α → α → ℝ)
    (k : ℕ) (v u : α) : ℝ :=
  ∑ t : Fin k → α, forwardPathWeight p v (Fin.snoc t u)

theorem markedReturnWeight_nonneg {α : Type*} [Fintype α] (p : α → α → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (k : ℕ) (v u : α) :
    0 ≤ markedReturnWeight p k v u :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => hp _ _

theorem markedReturnWeight_sum_le {α : Type*} [Fintype α] (p : α → α → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, p i j ≤ C) (k : ℕ) (v : α) :
    (∑ u, markedReturnWeight p k v u) ≤ C^(k+1) := by
  have heq : (∑ u, markedReturnWeight p k v u) =
      ∑ t : Fin (k+1) → α, forwardPathWeight p v t := by
    unfold markedReturnWeight
    have h := Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (k+1) => α))
      (fun ut : α × (Fin k → α) => forwardPathWeight p v (Fin.snoc ut.2 ut.1))
      (fun t => forwardPathWeight p v t) (fun _ => rfl)
    simpa only [Fintype.sum_prod_type] using h
  rw [heq]
  exact forwardPathWeight_sum_le p hp C hC hrow (k+1) v

/-- The manuscript's marked-edge estimate for the actual common ghost
background. Its scalar envelope is a local helper premise, to be discharged
separately on late source shells and on the retained interior labels. -/
theorem ghost_marked_edge_bound {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S : Finset (Fin n)) (t d : ℝ) (hd : 0 ≤ d)
    (henvelope : ∀ u ∈ S, w.rate u * Real.exp (-w.rate u*t) ≤ d) :
    (∑ v ∈ Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t),
      ∑ u ∈ S, w.rate u * Real.exp (-w.rate u*t) *
        markedReturnWeight (ghostEntry w ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) * d := by
  classical
  let C : ℝ := (2*ell+1 : ℕ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hp (i j : Fin n) : 0 ≤ ghostEntry w ell old i j := (ghostEntry_mem_Icc w ell old i j).1
  have hreturn (v : Fin n) := markedReturnWeight_sum_le (ghostEntry w ell old)
    hp C hC (ghostEntry_row_bound w ell old hnonneg) k v
  have hpoint (v : Fin n) :
      (∑ u ∈ S, w.rate u * Real.exp (-w.rate u*t) *
        markedReturnWeight (ghostEntry w ell old) k v u) ≤ d*C^(k+1) := by
    calc
      _ ≤ ∑ u ∈ S, d * markedReturnWeight (ghostEntry w ell old) k v u :=
        Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_right (henvelope u hu)
          (markedReturnWeight_nonneg _ hp k v u)
      _ ≤ ∑ u : Fin n, d * markedReturnWeight (ghostEntry w ell old) k v u :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun u _ _ => mul_nonneg hd (markedReturnWeight_nonneg _ hp k v u))
      _ ≤ d*C^(k+1) := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hreturn v) hd
  calc
    _ ≤ ∑ _v ∈ Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t), d*C^(k+1) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = ((Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t)).card : ℝ) * (d*C^(k+1)) := by simp
    _ ≤ C * (d*C^(k+1)) := mul_le_mul_of_nonneg_right
      (by dsimp [C]; exact_mod_cast ghostWindowByOrder_multiplicity_le old hinj hnonneg ell t) (by positivity)
    _ = _ := by change C*(d*C^(k+1)) = C^(k+2)*d; rw [show k+2 = (k+1)+1 by omega, pow_succ]; ring

end Luce
