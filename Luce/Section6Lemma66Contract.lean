import Luce.Section5CycleProbability
import Mathlib.Probability.HasLaw

/-! Independent closed statement of Lemma 6.6 in
`fixed_points_sampled_profile.tex`. The constant precedes the probability
space, number of clocks, densities, and selected label set. The counted
quantity is written out, without using a proof-side counting definition. -/

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal
universe u
namespace Luce.Section6.Lemma66Contract
attribute [local instance] Classical.propDecidable

def lemma66 : Prop :=
  ∀ ell : ℕ, 1 ≤ ell → ∃ K : ℝ, 0 < K ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (n : ℕ) (E : Fin n → Ω → ℝ) (g : Fin n → ℝ → ℝ≥0∞),
      (∀ i, HasLaw (E i) (volume.withDensity (g i)) P) →
      iIndepFun E P → ∀ (S : Finset (Fin n)) (h : ℝ → ℝ),
      (∀ t, 0 ≤ h t) → Integrable h →
      (∀ i ∈ S, ∀ t, g i t ≤ ENNReal.ofReal (h t)) →
      Integrable (fun ω => ((S.filter fun i =>
        minimalPeriod (raceRankPermutation (fun j => E j ω) : Fin n → Fin n) i = ell).card : ℝ)) P ∧
      (∫ ω, ((S.filter fun i =>
        minimalPeriod (raceRankPermutation (fun j => E j ω) : Fin n → Fin n) i = ell).card : ℝ) ∂P)
        ≤ K * ∫ t, h t

end Luce.Section6.Lemma66Contract
