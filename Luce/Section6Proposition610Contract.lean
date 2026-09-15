import Luce.Section6CoreCategoryDefinitions
import Luce.Section6Sampling

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6.Proposition610Contract

/-- Closed target for manuscript Proposition 6.10 (Core factorial moments).
The categories use the original largest-label root convention; their
mean is the literal distinct-vertex ideal sum. -/
def proposition610 : Prop :=
  ∀ (f : ℝ → ℝ) (left right : EndpointBehavior), PowerProfile f left right →
  ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
  ∀ (q : ℕ) (c : Fin q → CoreCycleCategory),
    (∀ i, (cornerBehavior left right (c i).side).active) → CoreCategoriesDisjoint c →
  ∀ r : Fin q → ℕ, ∃ C kappa : ℝ, 0 < C ∧ 0 < kappa ∧ ∃ K N : ℕ, 2 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      |(∫ clocks, ∏ i : Fin q,
          ((coreCategoryCount (raceRankPermutation clocks) (c i)).descFactorial (r i) : ℝ)
            ∂exponentialRace (w n)) -
        ∏ i, (coreCategoryIdealMean left right n (c i))^(r i)| ≤
      C*(1+Real.log (n : ℝ))^K*(idealCoreLower n : ℝ)^(-kappa)

end Luce.Section6.Proposition610Contract
