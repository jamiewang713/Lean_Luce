import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic

/-!
# Predictable truncation by compensator mass

The recursive indicators `H_{n,k}` in the proof of Lemma
`lem:predictable-poisson`, with indices shifted to start at zero.
-/

open scoped BigOperators
open MeasureTheory

namespace Luce

/-- Accumulated compensator after discarding terms that violate either cap. -/
noncomputable def stoppedMass (p : ℕ → ℝ) (δ K : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if p k ≤ δ ∧ stoppedMass p δ K k + p k ≤ K
    then stoppedMass p δ K k + p k else stoppedMass p δ K k

/-- The predictable acceptance test before draw `k`. -/
def keepTerm (p : ℕ → ℝ) (δ K : ℝ) (k : ℕ) : Prop :=
  p k ≤ δ ∧ stoppedMass p δ K k + p k ≤ K

/-- Conditional probability retained by the truncation. -/
noncomputable def stoppedProbability (p : ℕ → ℝ) (δ K : ℝ) (k : ℕ) : ℝ := by
  classical
  exact if keepTerm p δ K k then p k else 0

lemma stoppedMass_succ (p : ℕ → ℝ) (δ K : ℝ) (k : ℕ) :
    stoppedMass p δ K (k + 1) = stoppedMass p δ K k + stoppedProbability p δ K k := by
  by_cases h : p k ≤ δ ∧ stoppedMass p δ K k + p k ≤ K
  · simp [stoppedMass, stoppedProbability, keepTerm, h]
  · simp [stoppedMass, stoppedProbability, keepTerm, h]

lemma stoppedProbability_nonneg {p : ℕ → ℝ} {δ K : ℝ} {k : ℕ}
    (hp : 0 ≤ p k) : 0 ≤ stoppedProbability p δ K k := by
  unfold stoppedProbability
  split_ifs <;> linarith

lemma stoppedProbability_le {p : ℕ → ℝ} {δ K : ℝ} {k : ℕ}
    (hp : 0 ≤ p k) : stoppedProbability p δ K k ≤ p k := by
  unfold stoppedProbability
  split_ifs <;> linarith

lemma stoppedProbability_le_cap (p : ℕ → ℝ) {δ K : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    stoppedProbability p δ K k ≤ δ := by
  unfold stoppedProbability
  split_ifs with h
  · exact h.1
  · exact hδ

lemma stoppedMass_nonneg {p : ℕ → ℝ} {δ K : ℝ} (hp : ∀ k, 0 ≤ p k) (k : ℕ) :
    0 ≤ stoppedMass p δ K k := by
  induction k with
  | zero => simp [stoppedMass]
  | succ k ih => rw [stoppedMass_succ]; exact add_nonneg ih (stoppedProbability_nonneg (hp k))

lemma stoppedMass_le_cap (p : ℕ → ℝ) {δ K : ℝ} (hK : 0 ≤ K) (k : ℕ) :
    stoppedMass p δ K k ≤ K := by
  induction k with
  | zero => exact hK
  | succ k ih =>
    simp only [stoppedMass]
    split_ifs with h
    · exact h.2
    · exact ih

/-- The recursive accumulator is exactly the sum of retained probabilities. -/
lemma sum_stoppedProbability (p : ℕ → ℝ) (δ K : ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, stoppedProbability p δ K j) = stoppedMass p δ K k := by
  induction k with
  | zero => simp [stoppedMass]
  | succ k ih => rw [Finset.sum_range_succ, stoppedMass_succ, ih]

lemma stoppedMass_le_sum {p : ℕ → ℝ} {δ K : ℝ} (hp : ∀ k, 0 ≤ p k) (k : ℕ) :
    stoppedMass p δ K k ≤ ∑ j ∈ Finset.range k, p j := by
  rw [← sum_stoppedProbability]
  exact Finset.sum_le_sum (fun j _ => stoppedProbability_le (hp j))

/-- On the good event for the original array, every test is accepted. -/
theorem keepTerm_of_total_le {p : ℕ → ℝ} {δ K : ℝ} {N : ℕ}
    (hp : ∀ k, 0 ≤ p k) (hcap : ∀ k < N, p k ≤ δ)
    (htotal : ∑ j ∈ Finset.range N, p j ≤ K) {k : ℕ} (hk : k < N) :
    keepTerm p δ K k := by
  refine ⟨hcap k hk, ?_⟩
  calc
    stoppedMass p δ K k + p k ≤ (∑ j ∈ Finset.range k, p j) + p k :=
      add_le_add (stoppedMass_le_sum hp k) le_rfl
    _ = ∑ j ∈ Finset.range (k + 1), p j := (Finset.sum_range_succ _ _).symm
    _ ≤ ∑ j ∈ Finset.range N, p j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt hk))
        (fun j _ _ => hp j)
    _ ≤ K := htotal

theorem stoppedProbability_eq_of_total_le {p : ℕ → ℝ} {δ K : ℝ} {N : ℕ}
    (hp : ∀ k, 0 ≤ p k) (hcap : ∀ k < N, p k ≤ δ)
    (htotal : ∑ j ∈ Finset.range N, p j ≤ K) {k : ℕ} (hk : k < N) :
    stoppedProbability p δ K k = p k := by
  exact if_pos (keepTerm_of_total_le hp hcap htotal hk)

/-- A deletion entails either an excessive original atom or excessive original
total mass; this is the event inclusion used to remove the truncation. -/
theorem deletion_subset {p : ℕ → ℝ} {δ K : ℝ} {N : ℕ}
    (hp : ∀ k, 0 ≤ p k) (hdelete : ∃ k < N, ¬keepTerm p δ K k) :
    (∃ k < N, δ < p k) ∨ K < ∑ j ∈ Finset.range N, p j := by
  by_contra h
  push Not at h
  obtain ⟨k, hk, hbad⟩ := hdelete
  exact hbad (keepTerm_of_total_le hp h.1 h.2 hk)

section Measurability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The cap is predictable because it only uses the current predictable
probability and probabilities from earlier draws. -/
theorem measurable_stoppedMass (ℱ : Filtration ℕ mΩ) (p : ℕ → Ω → ℝ)
    (hp : ∀ k, Measurable[ℱ k] (p k)) (δ K : ℝ) :
    ∀ k, Measurable[ℱ k] (fun ω => stoppedMass (fun j => p j ω) δ K k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hp' := (hp k).mono (ℱ.mono (Nat.le_succ k)) le_rfl
    have ih' := ih.mono (ℱ.mono (Nat.le_succ k)) le_rfl
    have hset : MeasurableSet[ℱ (k + 1)]
        {ω | p k ω ≤ δ ∧ stoppedMass (fun j => p j ω) δ K k + p k ω ≤ K} :=
      (measurableSet_le hp' measurable_const).inter
        (measurableSet_le (ih'.add hp') measurable_const)
    exact (ih'.add hp').ite hset ih'

theorem measurableSet_keepTerm (ℱ : Filtration ℕ mΩ) (p : ℕ → Ω → ℝ)
    (hp : ∀ k, Measurable[ℱ k] (p k)) (δ K : ℝ) (k : ℕ) :
    MeasurableSet[ℱ k] {ω | keepTerm (fun j => p j ω) δ K k} :=
  (measurableSet_le (hp k) measurable_const).inter
    (measurableSet_le ((measurable_stoppedMass ℱ p hp δ K k).add (hp k)) measurable_const)

theorem measurable_stoppedProbability (ℱ : Filtration ℕ mΩ) (p : ℕ → Ω → ℝ)
    (hp : ∀ k, Measurable[ℱ k] (p k)) (δ K : ℝ) (k : ℕ) :
    Measurable[ℱ k] (fun ω => stoppedProbability (fun j => p j ω) δ K k) :=
  (hp k).ite (measurableSet_keepTerm ℱ p hp δ K k) measurable_const

end Measurability
end Luce
