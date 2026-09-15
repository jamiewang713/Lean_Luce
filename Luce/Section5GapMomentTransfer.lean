import Luce.Section5GapLaw
import Luce.Section5GapMoments

/-!
# Exact mixed moments of the actual normalized race gaps

Source: `fixed_points.tex:1025–1048`. The coordinates selected here are
distinct actual gaps. Their joint law was proved from the race, and their
integrability is transferred before any real expectation is evaluated.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Luce

theorem integrable_selectedNormalizedGaps {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) (H : (Fin r → ℝ) → ℝ)
    (hH : Integrable H (standardGapLaw r)) :
    Integrable (fun c => H (fun a => raceNormalizedGaps w c (q a))) (exponentialRace w) :=
  (measurePreserving_selectedNormalizedGaps w q).integrable_comp_of_integrable hH

theorem integral_selectedNormalizedGaps {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) (H : (Fin r → ℝ) → ℝ)
    (hH : Integrable H (standardGapLaw r)) :
    (∫ c, H (fun a => raceNormalizedGaps w c (q a)) ∂exponentialRace w) =
      ∫ u, H u ∂standardGapLaw r := by
  have hp := measurePreserving_selectedNormalizedGaps w q
  have hm : AEStronglyMeasurable H ((exponentialRace w).map
      (fun c => fun a => raceNormalizedGaps w c (q a))) := by
    rw [hp.map_eq]
    exact hH.aestronglyMeasurable
  rw [← integral_map hp.measurable.aemeasurable hm, hp.map_eq]

/-- All mixed natural moments of distinct actual normalized gaps are
integrable, with no rate bound and no assumption of gap independence. -/
theorem integrable_selectedNormalizedGaps_mixed {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) (p : Fin r → ℕ) :
    Integrable (fun c => ∏ a, raceNormalizedGaps w c (q a) ^ p a) (exponentialRace w) :=
  integrable_selectedNormalizedGaps w q _ (integrable_mixed_expMeasure_one p)

/-- The exact mixed moment is the product of factorials. This includes
zero powers and the empty selection. -/
theorem integral_selectedNormalizedGaps_mixed {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) (p : Fin r → ℕ) :
    (∫ c, ∏ a, raceNormalizedGaps w c (q a) ^ p a ∂exponentialRace w) =
      ∏ a, ((p a).factorial : ℝ) := by
  rw [integral_selectedNormalizedGaps w q _ (integrable_mixed_expMeasure_one p)]
  exact integral_mixed_expMeasure_one p

theorem integrable_selectedNormalizedGaps_taylorEnvelope {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) :
    Integrable (fun c => (∑ a, raceNormalizedGaps w c (q a)) *
      ∏ a, raceNormalizedGaps w c (q a)) (exponentialRace w) :=
  integrable_selectedNormalizedGaps w q _ integrable_sum_mul_prod_expMeasure_one

/-- The multigap Taylor envelope for the actual race has expectation 2r,
uniformly over every positive weight array and all distinct chosen gaps. -/
theorem integral_selectedNormalizedGaps_taylorEnvelope {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) :
    (∫ c, (∑ a, raceNormalizedGaps w c (q a)) *
      ∏ a, raceNormalizedGaps w c (q a) ∂exponentialRace w) = 2 * (r : ℝ) := by
  rw [integral_selectedNormalizedGaps w q _ integrable_sum_mul_prod_expMeasure_one]
  simpa only [standardGapLaw, Fintype.card_fin] using
    (integral_sum_mul_prod_expMeasure_one (ι := Fin r))

end Luce
