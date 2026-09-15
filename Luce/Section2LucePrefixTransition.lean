import Luce.Section2LucePrefixRecursion
import Luce.Section2HistoryAtoms

/-! # Exact one-step identities for Luce prefix masses

These deterministic identities connect the defining permutation mass with
the remaining-label set. They are auxiliary to the approved conditional-law
statement and introduce no probability assumptions.
-/

open scoped BigOperators

namespace Luce

theorem remaining_total_eq_tail_sum {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    w.total (remaining σ k) =
      ∑ j ∈ Finset.univ.filter (k ≤ ·), w.rate (σ j) := by
  classical
  simp only [Weights.total, remaining, Finset.sum_filter]
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp σ (fun i => if k ≤ σ.symm i then w.rate i else 0)).symm

theorem prefixMass_succ {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    prefixMass w σ (k.val + 1) =
      prefixMass w σ k.val * (w.rate (σ k) / w.total (remaining σ k)) := by
  classical
  have hset : Finset.univ.filter (fun r : Fin n => r.val < k.val + 1) =
      insert k (Finset.univ.filter (fun r : Fin n => r.val < k.val)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Fin.ext_iff]
    omega
  simp only [prefixMass]
  rw [hset, Finset.prod_insert (by simp), remaining_total_eq_tail_sum]
  exact mul_comm _ _

/-- Agreement on the prefix fixes every factor in its partial Luce mass.
The identity holds even when `m ≥ n`, since both prefixes then include all
draw positions. -/
theorem prefixMass_eq_of_prefix_agreement {n : ℕ} (w : Weights n)
    (σ τ : Equiv.Perm (Fin n)) (m : ℕ) (hprefix : prefixAgrees σ τ m) :
    prefixMass w σ m = prefixMass w τ m := by
  classical
  apply Finset.prod_congr rfl
  intro r hr
  have hrm : r.val < m := (Finset.mem_filter.mp hr).2
  have hrem : remaining σ r = remaining τ r :=
    remaining_eq_of_prefix_agreement σ τ r (fun j hj => hprefix j (lt_trans hj hrm))
  rw [← remaining_total_eq_tail_sum w σ r, ← remaining_total_eq_tail_sum w τ r,
    hrem, hprefix r hrm]

/-- Any available label can be chosen next while preserving all preceding
draws. The representative is obtained by swapping that label with the
current next label in the output of the permutation. -/
theorem exists_prefixAgrees_next_eq {n : ℕ} (σ : Equiv.Perm (Fin n))
    (k i : Fin n) (havailable : k ≤ σ.symm i) :
    ∃ τ : Equiv.Perm (Fin n), prefixAgrees σ τ k.val ∧ τ k = i := by
  classical
  refine ⟨σ.trans (Equiv.swap (σ k) i), ?_, ?_⟩
  · intro j hj
    have hji : σ j ≠ i := (inverse_ge_iff_no_earlier_draw σ k i).mp havailable j hj
    have hjk : σ j ≠ σ k := fun h =>
      (ne_of_lt hj) (congrArg Fin.val (σ.injective h))
    simp only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hjk hji]
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]

end Luce
