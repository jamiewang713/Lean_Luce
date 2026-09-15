import Luce.Section5MarkedCoefficientLimit
import Luce.Section5FiniteTaylor
import Luce.Section5GapProductExpectation

/-!
# Uniform expectation limit for the actual marked-gap coefficient

Source: `fixed_points.tex:1035–1048`. This module applies the expectation
transfer to the actual deleted race. The finite configuration type below
only groups finite indices; its validity predicate is exposed at the
theorem boundary and is later proved from sorted marked ranks.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped BigOperators Topology ENNReal

namespace Luce
set_option backward.isDefEq.respectTransparency false

/-- Finite index data for a selection of distinct deleted gaps. This
auxiliary representation contains no probability or convergence facts. -/
structure MarkedGapIndexData (n r : ℕ) where
  removed : Finset (Fin n)
  labels : Fin r → Fin n
  ranks : Fin r → Fin n
  gaps : Fin r ↪ Fin (Finset.univ \ removed).card

/-- Uniform expectation convergence for the actual coefficient and actual
normalized gaps, with their moment hypotheses fully discharged. -/
theorem section5_marked_coefficient_expectation
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ removed : Finset (Fin n), ∀ u j : Fin r → Fin n,
        ∀ q : Fin r ↪ Fin (Finset.univ \ removed).card,
          ValidMarkedGapConfiguration (w n) α M removed u j q →
            (∫ old, |markedGapCoefficient (w n) removed u q old -
                ∏ a, profileGapCoefficient f ((w n).rate (u a))
                  (((j a).val + (1 : ℝ)) / n)| *
              (∏ a, markedNormalizedGaps (w n) removed q old a) ∂exponentialRace (w n)) < ε := by
  let I (n : ℕ) := {c : MarkedGapIndexData n r //
    ValidMarkedGapConfiguration (w n) α M c.removed c.labels c.ranks c.gaps}
  let A (n : ℕ) (c : I n) (old : Fin n → ℝ) (a : Fin r) :=
    markedGapScalar (w n) c.val.removed old (c.val.labels a) (c.val.gaps a)
  let B (n : ℕ) (c : I n) (a : Fin r) :=
    profileGapCoefficient f ((w n).rate (c.val.labels a))
      (((c.val.ranks a).val + (1 : ℝ)) / n)
  let U (n : ℕ) (c : I n) (old : Fin n → ℝ) :=
    markedGapCoefficient (w n) c.val.removed c.val.labels c.val.gaps old - ∏ a, B n c a
  let Y (n : ℕ) (c : I n) (old : Fin n → ℝ) :=
    ∏ a, markedNormalizedGaps (w n) c.val.removed c.val.gaps old a
  have hU (n : ℕ) (c : I n) : Measurable (U n c) :=
    (measurable_markedGapCoefficient (w n) c.val.removed c.val.labels c.val.gaps).sub measurable_const
  have hY (n : ℕ) (c : I n) : Integrable (Y n c) (exponentialRace (w n)) := by
    simpa only [Y, pow_one] using
      integrable_markedNormalizedGaps_mixed (w n) c.val.removed c.val.gaps (fun _ => 1)
  have hY2 (n : ℕ) (c : I n) : Integrable (fun old => Y n c old ^ 2) (exponentialRace (w n)) := by
    simpa only [Y, Finset.prod_pow] using
      integrable_markedNormalizedGaps_mixed (w n) c.val.removed c.val.gaps (fun _ => 2)
  have hY0 (n : ℕ) (c : I n) : ∀ᵐ old ∂exponentialRace (w n), 0 ≤ Y n c old := by
    filter_upwards [exponentialRace_injective_ae (w n), exponentialRace_nonnegative_background (w n)]
      with old hold hpos
    apply Finset.prod_nonneg
    intro a _
    exact raceNormalizedGaps_nonneg (compactDeletedWeights (w n) c.val.removed)
      (compactDeletedClocks c.val.removed old)
      (compactDeletedClocks_injective c.val.removed old hold)
      (fun k => hpos (deletedClockLabel c.val.removed k)) (c.val.gaps a)
  have hEY (n : ℕ) (c : I n) : (∫ old, Y n c old ∂exponentialRace (w n)) = 1 :=
    integral_markedNormalizedGaps_prod (w n) c.val.removed c.val.gaps
  have hEY2 (n : ℕ) (c : I n) : (∫ old, Y n c old ^ 2 ∂exponentialRace (w n)) ≤ (2 : ℝ) ^ r :=
    (integral_markedNormalizedGaps_prod_sq (w n) c.val.removed c.val.gaps).le
  obtain ⟨C, hC, hbounds⟩ := hf.marked_gap_scalar_uniform_bound r hα M hM
  have hAB : ∀ᶠ n : ℕ in atTop, ∀ c : I n, ∀ᵐ old ∂exponentialRace (w n),
      (∀ a, |A n c old a| ≤ C) ∧ (∀ a, |B n c a| ≤ C) := by
    filter_upwards [hbounds] with n hn c
    filter_upwards [exponentialRace_injective_ae (w n), exponentialRace_positive_background (w n)]
      with old hold hpos
    have hh := hn c.val.removed c.val.labels c.val.ranks c.val.gaps c.property old hold hpos
    exact ⟨fun a => (hh a).1, fun a => (hh a).2⟩
  have hscalar : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ c : I n,
        (exponentialRace (w n)).real {old | ∃ a, δ ≤ |A n c old a - B n c a|} < η := by
    intro δ hδ η hη
    have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (section5_uniform_marked_gap_coefficient w f hnorm hf r hα M hM δ hδ)
    have he : ∀ᶠ n : ℕ in atTop,
        (exponentialRace (w n)).real {old | MarkedCoefficientBad (w n) f r α M δ old} < η := by
      simpa only [ENNReal.toReal_zero, Measure.real, Function.comp_apply] using
        hlim.eventually (gt_mem_nhds hη)
    filter_upwards [he] with n hn c
    apply lt_of_le_of_lt _ hn
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    rintro old ⟨a, ha⟩
    exact ⟨c.val.removed, c.val.labels, c.val.ranks, c.val.gaps, c.property, a, ha⟩
  have hproducts := uniform_product_error_probability (fun n => exponentialRace (w n))
    A B hC.le hAB hscalar
  have hUbound : ∀ᶠ n : ℕ in atTop, ∀ c : I n, ∀ᵐ old ∂exponentialRace (w n),
      |U n c old| ≤ 2 * C ^ r := by
    filter_upwards [hAB] with n hn c
    filter_upwards [hn c] with old hold
    change |(∏ a, A n c old a) - ∏ a, B n c a| ≤ _
    exact (abs_sub _ _).trans (by linarith [abs_prod_le_uniform hold.1, abs_prod_le_uniform hold.2])
  have hUprob : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ c : I n,
        (exponentialRace (w n)).real {old | δ ≤ |U n c old|} < η := hproducts
  have hfinal := uniform_integral_error_mul_small (fun n => exponentialRace (w n)) U Y
    hU hY hY2 hY0 hEY (show 0 ≤ 2 * C ^ r by positivity)
    (show 0 ≤ (2 : ℝ) ^ r by positivity) hEY2 hUbound hUprob
  intro ε hε
  filter_upwards [hfinal ε hε] with n hn removed u j q hv
  exact hn ⟨⟨removed, u, j, q⟩, hv⟩

end Luce
