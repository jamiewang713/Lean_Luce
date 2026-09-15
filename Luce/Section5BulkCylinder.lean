import Luce.Section5Reservoir
import Luce.LuceNextDraw
import Luce.Section3RaceDrawLaw
import Mathlib.Order.Interval.Finset.Fin

/-!
# The weighted bulk cylinder bound

Source: `fixed_points.tex:1007–1033`, equation `eq:weighted-bulk-cylinder`.
This is the domination part of Lemma 5.2, not its local-limit conclusion.
We reorganize the source's exponential-memorylessness argument using the
equivalent sequential Luce draws. `sum_mass_prefix_next` derives the exact
one-step rule by summing full permutation masses. The reservoir bounds its
denominator uniformly over every history; successive prescribed ranks then
contribute successive factors. No boundedness of marked rates is imposed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Luce

attribute [local instance] Classical.propDecidable

/-- Sum the exact next-draw law over histories satisfying a preceding event.
This is the conditional-draw version of the memorylessness step at 1020–1033. -/
lemma sum_mass_event_next_le {n : ℕ} (w : Weights n) (k i : Fin n)
    (A : Equiv.Perm (Fin n) → Prop) [DecidablePred A] {c : ℝ}
    (hA : ∀ σ τ, prefixAgrees σ τ k.val → (A σ ↔ A τ))
    (hc : ∀ σ, w.choice (remaining σ k) i ≤ c) :
    (∑ τ : Equiv.Perm (Fin n), if A τ ∧ τ k = i then w.mass τ else 0) ≤
      c * ∑ τ : Equiv.Perm (Fin n), if A τ then w.mass τ else 0 := by
  classical
  let H := fun σ : Equiv.Perm (Fin n) => prefixVector σ k.val
  rw [← Finset.sum_fiberwise Finset.univ H
    (fun τ => if A τ ∧ τ k = i then w.mass τ else 0),
    ← Finset.sum_fiberwise Finset.univ H (fun τ => if A τ then w.mass τ else 0),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : ∃ σ, H σ = t
  · obtain ⟨σ, rfl⟩ := ht
    have hp (τ : Equiv.Perm (Fin n)) : H τ = H σ ↔ prefixAgrees σ τ k.val := by
      change prefixVector τ k.val = prefixVector σ k.val ↔ _
      rw [prefixVector_eq_iff]
      exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
    simp only [Finset.sum_filter, hp]
    have heq (τ : Equiv.Perm (Fin n)) :
        (if prefixAgrees σ τ k.val then
          if A τ ∧ τ k = i then w.mass τ else 0 else 0) =
        if A σ then
          if prefixAgrees σ τ k.val ∧ τ k = i then w.mass τ else 0 else 0 := by
      by_cases hp' : prefixAgrees σ τ k.val
      · by_cases hσ : A σ <;> simp [hp', ← hA σ τ hp', hσ]
      · simp [hp']
    have heq' (τ : Equiv.Perm (Fin n)) :
        (if prefixAgrees σ τ k.val then if A τ then w.mass τ else 0 else 0) =
        if A σ then if prefixAgrees σ τ k.val then w.mass τ else 0 else 0 := by
      by_cases hp' : prefixAgrees σ τ k.val
      · simp [hp', ← hA σ τ hp']
      · simp [hp']
    simp_rw [heq, heq']
    by_cases hσ : A σ
    · simp only [if_pos hσ]
      rw [sum_mass_prefix_next, sum_mass_prefix w σ k.val (Nat.le_of_lt k.isLt)]
      apply mul_le_mul_of_nonneg_right (hc σ)
      unfold prefixMass
      exact Finset.prod_nonneg fun _ _ => div_nonneg (w.positive _).le
        (Finset.sum_nonneg fun _ _ => (w.positive _).le)
    · simp [hσ]
  · have hempty : Finset.univ.filter (fun σ => H σ = t) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro σ _ hσ
      exact ht ⟨σ, hσ⟩
    simp [hempty]

/-- Iterate the one-step law at the prescribed ranks in increasing order.
The finite set records distinct ranks; repeated labels are allowed here
(their inconsistent assignment event has zero probability). -/
theorem sum_mass_cylinder_le {n : ℕ} (w : Weights n) (s : Finset (Fin n))
    (label : Fin n → Fin n) {B : ℝ} (hB : 0 < B)
    (hrem : ∀ k ∈ s, ∀ σ : Equiv.Perm (Fin n), B ≤ w.total (remaining σ k)) :
    (∑ σ : Equiv.Perm (Fin n),
      if ∀ k ∈ s, σ k = label k then w.mass σ else 0) ≤
        ∏ k ∈ s, w.rate (label k) / B := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp [w.sum_mass]
  | insert k s hks ih =>
    have hk : k ∉ s := fun hk => (lt_irrefl k) (hks k hk)
    have hrem' : ∀ j ∈ s, ∀ σ : Equiv.Perm (Fin n), B ≤ w.total (remaining σ j) :=
      fun j hj => hrem j (Finset.mem_insert_of_mem hj)
    have hstep := sum_mass_event_next_le w k (label k)
      (fun σ => ∀ j ∈ s, σ j = label j)
      (c := w.rate (label k) / B) (by
        intro σ τ hp
        constructor <;> intro h j hj
        · rw [← hp j (hks j hj)]
          exact h j hj
        · rw [hp j (hks j hj)]
          exact h j hj) (by
        intro σ
        unfold Weights.choice
        split_ifs
        · exact div_le_div_of_nonneg_left (w.positive _).le hB
            (hrem k (Finset.mem_insert_self k s) σ)
        · exact div_nonneg (w.positive _).le hB.le)
    have heq (σ : Equiv.Perm (Fin n)) :
        (∀ j ∈ insert k s, σ j = label j) ↔
          (∀ j ∈ s, σ j = label j) ∧ σ k = label k := by
      simp only [Finset.forall_mem_insert, and_comm]
    simp_rw [heq]
    rw [Finset.prod_insert hk]
    have hi : (∑ τ : Equiv.Perm (Fin n),
        if (fun σ => ∀ j ∈ s, σ j = label j) τ then w.mass τ else 0) ≤
        ∏ j ∈ s, w.rate (label j) / B := by
      simpa only using ih hrem'
    have hb := hstep.trans (mul_le_mul_of_nonneg_left hi
      (div_nonneg (w.positive _).le hB.le))
    simpa only using hb

/-- The removed labels before zero-based rank `k` have cardinality `k`.
This records the permutation multiplicity used in applying the reservoir. -/
lemma card_removed_before_rank {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    (Finset.univ \ remaining σ k).card = k.val := by
  classical
  have hs : Finset.univ \ remaining σ k = (Finset.Iio k).map σ.toEmbedding := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, remaining, Finset.mem_filter,
      true_and, not_le, Finset.mem_map, Finset.mem_Iio, Equiv.toEmbedding_apply]
    constructor
    · intro hi
      exact ⟨σ.symm i, hi, σ.apply_symm_apply i⟩
    · rintro ⟨j, hj, rfl⟩
      simpa only [Equiv.symm_apply_apply] using hj
  rw [hs, Finset.card_map, Fin.card_Iio]

/-- The reservoir controls every actual draw-history denominator up to `α n`.
Neither the history nor the set of marked labels is fixed in advance. -/
theorem ProfileLimit.eventually_bulk_remaining_rate {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin n, (k.val : ℝ) + 1 ≤ α * n →
        ∀ σ : Equiv.Perm (Fin n), b * n ≤ (w n).total (remaining σ k) := by
  obtain ⟨d, η, hd, hη, _, hleft⟩ := hf.moderate_reservoir_with_remaining_rate hα
  refine ⟨d * η, mul_pos hd hη, ?_⟩
  filter_upwards [hleft 0] with n hn k hk σ
  have hrem : ((Finset.univ \ remaining σ k).card : ℝ) ≤ α * n + (0 : ℕ) := by
    rw [card_removed_before_rank]
    push_cast
    linarith
  have h := hn (Finset.univ \ remaining σ k) hrem
  rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] at h
  exact h

/-- Distinct ranks are encoded by an embedding, and their products are
transported without an extra factorial. The labels need not be distinct for
this stronger auxiliary estimate. -/
theorem sum_mass_marked_cylinder_le {n r : ℕ} (w : Weights n)
    (i : Fin r → Fin n) (j : Fin r ↪ Fin n) {B : ℝ} (hB : 0 < B)
    (hrem : ∀ a : Fin r, ∀ σ : Equiv.Perm (Fin n), B ≤ w.total (remaining σ (j a))) :
    (∑ σ : Equiv.Perm (Fin n), if ∀ a, σ (j a) = i a then w.mass σ else 0) ≤
      (∏ a : Fin r, w.rate (i a)) / B ^ r := by
  classical
  let label : Fin n → Fin n := Function.extend j i id
  have hlabel (a : Fin r) : label (j a) = i a := j.injective.extend_apply i id a
  have h := sum_mass_cylinder_le w (Finset.univ.map j) label hB (by
    intro k hk
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hk
    exact hrem a)
  simpa only [Finset.forall_mem_map, Finset.mem_univ, forall_true_left,
    hlabel, Finset.prod_map, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_map, Finset.card_univ, Fintype.card_fin] using h

/-- Actual exponential-race events have the finite sums of the full Luce
masses, by the previously proved law of the sorted clocks. -/
lemma raceDraw_event_probability {n : ℕ} (w : Weights n)
    (A : Equiv.Perm (Fin n) → Prop) [DecidablePred A] :
    (exponentialRace w).real {clocks | A (raceDraw clocks)} =
      ∑ σ : Equiv.Perm (Fin n), if A σ then w.mass σ else 0 := by
  classical
  let s := Finset.univ.filter A
  have h := sum_measureReal_preimage_singleton (μ := exponentialRace w) s
    (f := raceDraw) (fun σ _ => (measurable_raceDraw n) (by trivial))
    (fun _ _ => measure_ne_top _ _)
  have he : raceDraw ⁻¹' (s : Set (Equiv.Perm (Fin n))) =
      {clocks | A (raceDraw clocks)} := by
    ext clocks
    simp only [Set.mem_preimage, Finset.mem_coe, s, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  rw [he] at h
  rw [← h]
  simp only [s, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs
  · exact raceDraw_mass w σ
  · rfl

/-- Equation `eq:weighted-bulk-cylinder` in draw-order notation. The same
constant works for every choice of distinct labels and distinct bulk ranks.
The empty tuple is also included and gives the identity probability one. -/
theorem ProfileLimit.weighted_bulk_draw_cylinder {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a : Fin r, ((j a).val : ℝ) + 1 ≤ α * n) →
        (exponentialRace (w n)).real {clocks | ∀ a, raceDraw clocks (j a) = i a} ≤
          K / (n : ℝ) ^ r * ∏ a : Fin r, (w n).rate (i a) := by
  obtain ⟨b, hb, hrem⟩ := hf.eventually_bulk_remaining_rate hα
  refine ⟨(b ^ r)⁻¹, inv_pos.mpr (pow_pos hb r), ?_⟩
  filter_upwards [hrem, eventually_gt_atTop 0] with n hn hnpos i j hj
  rw [raceDraw_event_probability (w n) (fun σ => ∀ a, σ (j a) = i a)]
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have h := sum_mass_marked_cylinder_le (w n) i j (mul_pos hb hn')
    (fun a => hn (j a) (hj a))
  calc
    _ ≤ (∏ a : Fin r, (w n).rate (i a)) / (b * n) ^ r := h
    _ = (b ^ r)⁻¹ / (n : ℝ) ^ r * ∏ a : Fin r, (w n).rate (i a) := by
      rw [mul_pow]
      field_simp

/-- Exact conversion from the paper's one-based rank convention to the
inverse draw permutation, on the full-probability event of distinct clocks. -/
lemma raceRank_eq_iff_raceDraw {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (i j : Fin n) :
    raceRank clocks i = j.val + 1 ↔ raceDraw clocks j = i := by
  rw [raceDraw_eq clocks hinj, drawPermutation, Equiv.symm_apply_eq, Fin.ext_iff]
  change 1 + (Finset.univ.filter (fun a => clocks a < clocks i)).card = j.val + 1 ↔
    j.val = (Finset.univ.filter (fun a => clocks a < clocks i)).card
  omega

/-- Equation `eq:weighted-bulk-cylinder` in the paper's exact rank convention.
All marked rates are unrestricted. Constants are uniform over distinct
marked labels and distinct prescribed ranks, and row zero is only omitted
by an eventual threshold. The case `r = 0` is proved as well. -/
theorem ProfileLimit.weighted_bulk_cylinder {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a : Fin r, ((j a).val : ℝ) + 1 ≤ α * n) →
        (exponentialRace (w n)).real
          {clocks | ∀ a, raceRank clocks (i a) = (j a).val + 1} ≤
          K / (n : ℝ) ^ r * ∏ a : Fin r, (w n).rate (i a) := by
  obtain ⟨K, hK, hbound⟩ := hf.weighted_bulk_draw_cylinder r hα
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with n hn i j hj
  have heq : {clocks | ∀ a, raceRank clocks (i a) = (j a).val + 1} =ᵐ[exponentialRace (w n)]
      {clocks | ∀ a, raceDraw clocks (j a) = i a} := by
    filter_upwards [exponentialRace_injective_ae (w n)] with clocks hinj
    apply propext
    exact forall_congr' (fun a => raceRank_eq_iff_raceDraw clocks hinj (i a) (j a))
  rw [measureReal_congr heq]
  exact hn i j hj

end Luce
