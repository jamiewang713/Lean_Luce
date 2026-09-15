import Luce.LuceMassRecursion

/-! # Finite prefixes of the Luce product law

Auxiliary exact products and agreement predicates for the approved
conditional-probability theorem. No prefix probability is assumed.
-/

open scoped BigOperators

namespace Luce

/-- Agreement on precisely the first `m` draw positions. -/
def prefixAgrees {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (m : ℕ) : Prop :=
  ∀ j : Fin n, j.val < m → σ j = τ j

/-- The product of the first `m` factors in the defining Luce mass. -/
noncomputable def prefixMass {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.univ.filter (fun r : Fin n => r.val < m),
    w.rate (σ r) / ∑ j ∈ Finset.univ.filter (r ≤ ·), w.rate (σ j)

lemma prefixAgrees_zero {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : prefixAgrees σ τ 0 := by
  simp [prefixAgrees]

lemma prefixAgrees_self {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    prefixAgrees σ σ m := fun _ _ => rfl

lemma prefixMass_zero {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n)) :
    prefixMass w σ 0 = 1 := by simp [prefixMass]

lemma prefixMass_full {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n)) :
    prefixMass w σ n = w.mass σ := by simp [prefixMass, Weights.mass]

/-- Removing the first draw leaves the same agreement condition on the tail. -/
lemma prefixAgrees_decomposeFin {n : ℕ} (p q : Fin (n + 1))
    (σ τ : Equiv.Perm (Fin n)) (m : ℕ) :
    prefixAgrees (Equiv.Perm.decomposeFin.symm (p, σ))
      (Equiv.Perm.decomposeFin.symm (q, τ)) (m + 1) ↔
      p = q ∧ prefixAgrees σ τ m := by
  simp only [prefixAgrees, Fin.forall_fin_succ,
    Equiv.Perm.decomposeFin_symm_apply_zero, Fin.val_zero, Nat.zero_lt_succ,
    forall_true_left, Equiv.Perm.decomposeFin_symm_apply_succ, Fin.val_succ,
    Nat.add_lt_add_iff_right]
  constructor
  · rintro ⟨hpq, htail⟩
    refine ⟨hpq, ?_⟩
    subst q
    intro j hj
    exact Fin.succ_inj.mp ((Equiv.swap 0 p).injective (htail j hj))
  · rintro ⟨rfl, htail⟩
    exact ⟨rfl, fun j hj => congrArg (fun a : Fin n => Equiv.swap 0 p a.succ) (htail j hj)⟩

/-- The first partial-product factor splits off with the same reduced weights
as the full Luce mass. -/
lemma prefixMass_decomposeFin {n : ℕ} (w : Weights (n + 1))
    (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    prefixMass w (Equiv.Perm.decomposeFin.symm (p, σ)) (m + 1) =
      (w.rate p / w.total Finset.univ) * prefixMass (w.removeFirst p) σ m := by
  classical
  simp only [prefixMass, Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  have hzero : (∑ j ∈ Finset.univ.filter ((0 : Fin (n + 1)) ≤ ·),
      w.rate (Equiv.Perm.decomposeFin.symm (p, σ) j)) = w.total Finset.univ := by
    simpa using w.sum_rate_perm (Equiv.Perm.decomposeFin.symm (p, σ))
  simp only [Fin.val_zero, Nat.zero_lt_succ, if_true,
    Equiv.Perm.decomposeFin_symm_apply_zero, hzero]
  congr 1
  apply Finset.prod_congr rfl
  intro r _
  simp only [Fin.val_succ, Nat.add_lt_add_iff_right]
  split_ifs
  · rw [Weights.decomposeFin_tail_sum, Equiv.Perm.decomposeFin_symm_apply_succ]
    rfl
  · rfl

end Luce
