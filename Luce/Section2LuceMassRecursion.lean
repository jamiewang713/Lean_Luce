import Luce.Section1Model
import Mathlib.GroupTheory.Perm.Fin

open scoped BigOperators

namespace Luce.Weights

/-- Weights remaining after selecting `p`, relabelled by swapping `p` with zero. -/
def removeFirst {n : ℕ} (w : Weights (n + 1)) (p : Fin (n + 1)) : Weights n where
  rate i := w.rate (Equiv.swap 0 p i.succ)
  positive _i := w.positive _

lemma sum_rate_perm {n : ℕ} (w : Weights n) (π : Equiv.Perm (Fin n)) :
    (∑ j, w.rate (π j)) = w.total Finset.univ := by
  exact Equiv.sum_comp π w.rate

lemma decomposeFin_tail_sum {n : ℕ} (w : Weights (n + 1))
    (p : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (r : Fin n) :
    (∑ j ∈ Finset.univ.filter (r.succ ≤ ·),
      w.rate (Equiv.Perm.decomposeFin.symm (p, τ) j)) =
    ∑ j ∈ Finset.univ.filter (r ≤ ·), (w.removeFirst p).rate (τ j) := by
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp [removeFirst]

/-- Splitting a Luce permutation mass into its first draw and remaining mass. -/
theorem mass_decomposeFin {n : ℕ} (w : Weights (n + 1))
    (p : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    w.mass (Equiv.Perm.decomposeFin.symm (p, τ)) =
      (w.rate p / w.total Finset.univ) * (w.removeFirst p).mass τ := by
  rw [mass, Fin.prod_univ_succ]
  simp only [Fin.zero_le, Finset.filter_true, Equiv.Perm.decomposeFin_symm_apply_zero]
  rw [sum_rate_perm]
  congr 1
  apply Finset.prod_congr rfl
  intro r _
  rw [decomposeFin_tail_sum, Equiv.Perm.decomposeFin_symm_apply_succ]
  rfl

/-- The defining Luce masses sum to one over all permutations. -/
theorem sum_mass {n : ℕ} (w : Weights n) :
    ∑ τ : Equiv.Perm (Fin n), w.mass τ = 1 := by
  induction n with
  | zero => simp [mass]
  | succ n ih =>
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm w.mass,
      Fintype.sum_prod_type]
    simp only [mass_decomposeFin, ← Finset.mul_sum, ih, mul_one]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (w.total_pos Finset.univ_nonempty).ne'

end Luce.Weights
