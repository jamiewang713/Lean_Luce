import Luce.Section6Lemma67Definitions

/-! Closed statement of Lemma 6.7 of fixed_points_sampled_profile.tex.
Only the original profile and exact sampling are mathematical inputs.
The constants precede n, cutoffs, sampling grid, and the cycle length.
Index k represents length k+1. Counts are actual cycles modulo rotation. -/
noncomputable section
open MeasureTheory
namespace Luce.Section6.Lemma67Contract

def endpointEstimates (f : ℝ → ℝ) (k : ℕ) (side : Corner)
    (C delta kappa : ℝ) : Prop :=
  ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
  (∀ (n : ℕ) (v : Fin n), (cornerDistance side v : ℝ)/(n : ℝ) ≤ delta →
    (∫ clocks, (selectedRootCycleCount (raceRankPermutation clocks) k {v} : ℝ)
      ∂exponentialRace (w n)) ≤ C/(cornerDistance side v : ℝ)) ∧
  (∀ (n : ℕ) (A B : ℝ), 1 ≤ A → A ≤ B → B/(n : ℝ) ≤ delta →
    (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) side k A B : ℝ)
      ∂exponentialRace (w n)) ≤ C) ∧
  (∀ (n : ℕ) (A B R : ℝ), 1 ≤ A → A ≤ B → B/(n : ℝ) ≤ delta → 1 ≤ R →
    (∫ clocks, (logarithmicExcursionCount (raceRankPermutation clocks) side k A B R : ℝ)
      ∂exponentialRace (w n)) ≤ C*(1+Real.log (B/A))*R^(-kappa))

def active : Prop :=
  ∀ (f : ℝ → ℝ) (left right : EndpointBehavior), PowerProfile f left right →
  ∀ L : ℕ, ∃ C delta kappa : ℝ,
    0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < kappa ∧
    ∀ k : ℕ, k < L → ∀ side : Corner, (cornerBehavior left right side).active →
      endpointEstimates f k side C delta kappa

/-- Roots separated from the active corners: includes every fixed middle
interval and fixed neighborhoods of all inactive endpoints. -/
def regular : Prop :=
  ∀ (f : ℝ → ℝ) (left right : EndpointBehavior), PowerProfile f left right →
  ∀ (L : ℕ) (eps : ℝ), 0 < eps → eps < 1 →
  ∃ C : ℝ, 0 < C ∧
  ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
  ∀ (n k : ℕ), k < L →
    (∫ clocks, (selectedRootCycleCount (raceRankPermutation clocks) k
      (offActiveLabels left right n eps) : ℝ) ∂exponentialRace (w n)) ≤ C

def lemma67 : Prop := active ∧ regular

end Luce.Section6.Lemma67Contract
