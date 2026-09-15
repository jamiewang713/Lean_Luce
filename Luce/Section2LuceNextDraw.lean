import Luce.Section2LucePrefixMass
import Luce.Section2LucePrefixTransition

/-! # Next-draw masses derived from the full Luce law

The sums in this file run over actual full permutations and use the exact
product mass from `eq:luce-law`. The next-draw rule is proved by summing
completions, not assumed as a probability hypothesis.
-/

open scoped BigOperators
open Classical

namespace Luce

lemma prefixAgrees_succ_iff {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (k : Fin n) :
    prefixAgrees σ τ (k.val + 1) ↔
      prefixAgrees σ τ k.val ∧ σ k = τ k := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h k (Nat.lt_succ_self _)⟩
  · rintro ⟨hprefix, hnext⟩ j hj
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | heq
    · exact hprefix j hlt
    · simpa only [Fin.ext heq] using hnext

/-- Total mass of all completions with a specified next draw. -/
theorem sum_mass_prefix_next {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (k i : Fin n) :
    (∑ τ : Equiv.Perm (Fin n),
      if prefixAgrees σ τ k.val ∧ τ k = i then w.mass τ else 0) =
      w.choice (remaining σ k) i * prefixMass w σ k.val := by
  classical
  by_cases havailable : k ≤ σ.symm i
  · obtain ⟨ρ, hσρ, hρk⟩ := exists_prefixAgrees_next_eq σ k i havailable
    have heq (τ : Equiv.Perm (Fin n)) :
        (prefixAgrees σ τ k.val ∧ τ k = i) ↔ prefixAgrees ρ τ (k.val + 1) := by
      rw [prefixAgrees_succ_iff]
      constructor
      · rintro ⟨hστ, hτk⟩
        exact ⟨fun j hj => (hσρ j hj).symm.trans (hστ j hj), hρk.trans hτk.symm⟩
      · rintro ⟨hρτ, hτk⟩
        exact ⟨fun j hj => (hσρ j hj).trans (hρτ j hj), hτk.symm.trans hρk⟩
    simp_rw [heq]
    rw [sum_mass_prefix w ρ (k.val + 1) (Nat.succ_le_of_lt k.isLt),
      prefixMass_succ, hρk,
      ← prefixMass_eq_of_prefix_agreement w σ ρ k.val hσρ,
      ← remaining_eq_of_prefix_agreement σ ρ k hσρ]
    have hchoice : w.choice (remaining σ k) i = w.rate i / w.total (remaining σ k) := by
      apply if_pos
      simpa only [remaining, Finset.mem_filter, Finset.mem_univ, true_and] using havailable
    rw [hchoice, mul_comm]
  · have hnone (τ : Equiv.Perm (Fin n)) : ¬(prefixAgrees σ τ k.val ∧ τ k = i) := by
      rintro ⟨hστ, hτk⟩
      have hrem := remaining_eq_of_prefix_agreement σ τ k hστ
      have hi : i ∈ remaining τ k := by
        rw [← hτk]
        simp [remaining]
      rw [← hrem] at hi
      exact havailable (Finset.mem_filter.mp hi).2
    simp only [hnone, if_false, Finset.sum_const_zero]
    have hchoice : w.choice (remaining σ k) i = 0 := by
      apply if_neg
      simpa only [remaining, Finset.mem_filter, Finset.mem_univ, true_and] using havailable
    rw [hchoice, zero_mul]

/-- The finite history-fiber identity for the fixed-point indicator. -/
theorem fixed_point_mass_fiber_identity {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    (∑ τ ∈ Finset.univ.filter
        (fun τ : Equiv.Perm (Fin n) => prefixVector τ k.val = prefixVector σ k.val),
      w.mass τ * (if τ.symm k = k then (1 : ℝ) else 0)) =
      predictableChance w σ k *
        ∑ τ ∈ Finset.univ.filter
          (fun τ : Equiv.Perm (Fin n) => prefixVector τ k.val = prefixVector σ k.val),
          w.mass τ := by
  classical
  have hprefix (τ : Equiv.Perm (Fin n)) :
      prefixVector τ k.val = prefixVector σ k.val ↔ prefixAgrees σ τ k.val := by
    rw [prefixVector_eq_iff]
    exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
  simp only [Finset.sum_filter, hprefix, inverse_fixed_iff]
  have hleft :
      (∑ τ : Equiv.Perm (Fin n), if prefixAgrees σ τ k.val then
        w.mass τ * (if τ k = k then (1 : ℝ) else 0) else 0) =
      ∑ τ : Equiv.Perm (Fin n),
        if prefixAgrees σ τ k.val ∧ τ k = k then w.mass τ else 0 := by
    apply Finset.sum_congr rfl
    intro τ _
    by_cases hp : prefixAgrees σ τ k.val <;> by_cases hf : τ k = k <;> simp [hp, hf]
  rw [hleft, sum_mass_prefix_next, sum_mass_prefix w σ k.val (Nat.le_of_lt k.isLt)]
  rfl

end Luce
