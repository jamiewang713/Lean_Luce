import Luce.Section2LucePrefixRecursion

open scoped BigOperators
open Classical

namespace Luce

/-- Summing the defining permutation masses over all completions of a prefix
gives exactly its truncated Luce product. -/
theorem sum_mass_prefix {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n) :
    (∑ τ : Equiv.Perm (Fin n), if prefixAgrees σ τ m then w.mass τ else 0) =
      prefixMass w σ m := by
  classical
  induction n generalizing m with
  | zero =>
    have hmzero : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    simp only [prefixAgrees_zero, if_true, prefixMass_zero]
    exact w.sum_mass
  | succ n ih =>
    cases m with
    | zero =>
      simp only [prefixAgrees_zero, if_true, prefixMass_zero]
      exact w.sum_mass
    | succ m =>
      obtain ⟨⟨p, σ⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective σ
      rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm
        (fun τ => if prefixAgrees (Equiv.Perm.decomposeFin.symm (p, σ)) τ (m + 1)
          then w.mass τ else 0), Fintype.sum_prod_type]
      simp only [prefixAgrees_decomposeFin, Weights.mass_decomposeFin]
      rw [Finset.sum_eq_single p]
      · simp only [true_and]
        have hfactor :
            (∑ τ : Equiv.Perm (Fin n), if prefixAgrees σ τ m then
              (w.rate p / w.total Finset.univ) * (w.removeFirst p).mass τ else 0) =
            (w.rate p / w.total Finset.univ) *
              ∑ τ : Equiv.Perm (Fin n),
                if prefixAgrees σ τ m then (w.removeFirst p).mass τ else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ _
          split_ifs <;> simp
        rw [hfactor, ih (w.removeFirst p) σ m (Nat.le_of_succ_le_succ hm),
          prefixMass_decomposeFin]
      · intro q _ hqp
        simp [Ne.symm hqp]
      · simp

end Luce
