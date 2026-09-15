import Luce.Section5WindowLength
import Luce.Section5Reservoir

/-!
# The interior expected-window estimate from the original assumptions

Source: `fixed_points.tex:1219–1224`. Discharge the finite occupation
bound's remaining-rate premise with Lemma 5.1. Constants are uniform in the
row and the interior label; no expected-gap hypothesis remains.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Luce
attribute [local instance] Classical.propDecidable

/-- The literal O(1/n) expected-window estimate, with integrability and
eventual interior index validity proved from the profile reservoir. -/
theorem ProfileLimit.interior_ghostWindowLength {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (ell : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ j : Fin n,
      (j.val : ℝ) + 1 ≤ α * n →
        Integrable (fun old => ghostWindowLength ell old j) (exponentialRace (w n)) ∧
        (∫ old, ghostWindowLength ell old j ∂exponentialRace (w n)) ≤ K / n := by
  obtain ⟨d, η, hd, hη, _, hrem⟩ := hf.moderate_reservoir_with_remaining_rate hα
  have hmargin : ∀ᶠ n : ℕ in atTop, (ell : ℝ) ≤ (1 - α) * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop ((ell : ℝ) / (1 - α)))] with n hn
    have h := (div_le_iff₀ (sub_pos.mpr hα)).mp hn
    linarith
  refine ⟨(2 * ell + 1 : ℕ) / (d * η), div_pos (by positivity) (mul_pos hd hη), ?_⟩
  filter_upwards [hrem ell, hmargin] with n hn hmar j hj
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
    have hN : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    have hidx : j.val + ell < n + 1 := by
      have hreal : (j.val : ℝ) + ell < (n + 1 : ℕ) := by nlinarith
      exact_mod_cast hreal
    have hB : 0 < d * η * ((n + 1 : ℕ) : ℝ) := mul_pos (mul_pos hd hη) hN
    have hr : ∀ k, k ≤ j.val + ell → ∀ s : Finset (Fin (n + 1)),
        s.card = (n + 1) - k → d * η * ((n + 1 : ℕ) : ℝ) ≤ (w (n + 1)).total s := by
      intro k hk s hs
      let removed := Finset.univ \ s
      have hcard : removed.card = k := by
        dsimp only [removed]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ,
          Fintype.card_fin, hs]
        omega
      have hbound : (removed.card : ℝ) ≤ α * ((n + 1 : ℕ) : ℝ) + ell := by
        rw [hcard]
        have hk' : (k : ℝ) ≤ (j.val : ℝ) + ell := by exact_mod_cast hk
        linarith
      have heq : Finset.univ \ removed = s := by
        ext i
        simp [removed]
      have h := hn removed hbound
      simpa only [heq, Weights.total] using h
    refine ⟨ghostWindowLength_integrable (w (n + 1)) ell j hidx _ hB hr, ?_⟩
    have h := ghostWindowLength_expectation_le (w (n + 1)) ell j hidx _ hB hr
    simpa only [div_div] using h

/-- One constant and one eventual row threshold work for every window size
through L, preserving the source's K_L uniformity. -/
theorem ProfileLimit.interior_ghostWindowLength_uniform {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (L : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ ell : ℕ, ell ≤ L → ∀ j : Fin n,
      (j.val : ℝ) + 1 ≤ α * n →
        Integrable (fun old => ghostWindowLength ell old j) (exponentialRace (w n)) ∧
        (∫ old, ghostWindowLength ell old j ∂exponentialRace (w n)) ≤ K / n := by
  choose K hKpos hK using fun ell : Fin (L + 1) =>
    hf.interior_ghostWindowLength ell.val hα
  refine ⟨∑ ell, K ell, Finset.sum_pos (fun ell _ => hKpos ell) Finset.univ_nonempty, ?_⟩
  have hall : ∀ᶠ n : ℕ in atTop, ∀ ell : Fin (L + 1), ∀ j : Fin n,
      (j.val : ℝ) + 1 ≤ α * n →
        Integrable (fun old => ghostWindowLength ell.val old j) (exponentialRace (w n)) ∧
        (∫ old, ghostWindowLength ell.val old j ∂exponentialRace (w n)) ≤ K ell / n :=
    Filter.eventually_all.mpr hK
  filter_upwards [hall] with n hn ell hell j hj
  let a : Fin (L + 1) := ⟨ell, by omega⟩
  have ha := hn a j hj
  refine ⟨ha.1, ha.2.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact Finset.single_le_sum (fun b _ => (hKpos b).le) (Finset.mem_univ a)

end Luce
