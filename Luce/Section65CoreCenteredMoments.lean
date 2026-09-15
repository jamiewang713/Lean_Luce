import Luce.Section65CorePolynomial
import Luce.Section65CenteringExpansion

noncomputable section
open MeasureTheory Filter Polynomial
open scoped Topology BigOperators
namespace Luce.Section6

variable (f : ℝ → ℝ) (left right : EndpointBehavior) (hp : PowerProfile f left right)
  (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
  (q : ℕ) (c : Fin q → CoreCycleCategory)
  (ha : ∀ i, (cornerBehavior left right (c i).side).active)
  (hd : CoreCategoriesDisjoint c)

include hp hs ha hd

/-- Centering preserves the rapidly vanishing factorial-moment error.
All mean factors remain explicit in this finite expansion. -/
theorem core_centered_moment_rapid65
    (hμ : ∀ i, LogGrowth65 (fun n => coreCategoryIdealMean left right n (c i)))
    (r : Fin q → ℕ) :
    RapidError65 (fun n => (∫ clocks, ∏ i : Fin q,
      ((coreCategoryCount (raceRankPermutation clocks) (c i) : ℝ)-
        coreCategoryIdealMean left right n (c i))^(r i) ∂exponentialRace (w n)) -
      ∏ i, centeredPoissonMoment65 (coreCategoryIdealMean left right n (c i)) (r i)) := by
  classical
  let μ (n : ℕ) (i : Fin q) := coreCategoryIdealMean left right n (c i)
  let V := (i : Fin q) → Fin (r i+1)
  let a (v : V) (n : ℕ) : ℝ :=
    ∏ i : Fin q, ((r i).choose (v i).val : ℝ)*(-μ n i)^(r i-(v i).val)
  let e (v : V) (n : ℕ) : ℝ :=
    (∫ clocks, ∏ i : Fin q, (coreCategoryCount (raceRankPermutation clocks) (c i) : ℝ)^(v i).val
      ∂exponentialRace (w n)) - ∏ i, poissonFunctional65 (μ n i) ((X : ℝ[X])^(v i).val)
  have he (n : ℕ) : (∫ clocks, ∏ i : Fin q,
      ((coreCategoryCount (raceRankPermutation clocks) (c i) : ℝ)-μ n i)^(r i)
        ∂exponentialRace (w n)) - ∏ i, centeredPoissonMoment65 (μ n i) (r i) =
          ∑ v : V, a v n*e v n := by
    simp_rw [centered_power_expansion65, centeredPoissonMoment65_expansion,
      Fintype.prod_sum, Finset.prod_mul_distrib]
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      dsimp [a,e]
      simp only [Finset.prod_mul_distrib]
      ring
    · intro v hv
      simpa only [Finset.prod_mul_distrib] using integrable_race_permutation_statistic (w n) (fun R =>
        (∏ i : Fin q, ((r i).choose (v i).val : ℝ)*(-μ n i)^(r i-(v i).val)) *
          ∏ i, (coreCategoryCount R (c i) : ℝ)^(v i).val)
  change RapidError65 (fun n => (∫ clocks, ∏ i : Fin q,
    ((coreCategoryCount (raceRankPermutation clocks) (c i) : ℝ)-μ n i)^(r i)
      ∂exponentialRace (w n)) - ∏ i, centeredPoissonMoment65 (μ n i) (r i))
  simp_rw [he]
  apply RapidError65.sum
  intro v hv
  have hv' : RapidError65 (e v) := by
    simpa [e, μ] using core_polynomial_rapid65 f left right hp grid w hs q c ha hd
      (fun i => (X : ℝ[X])^(v i).val)
  apply hv'.mul_growth
  apply LogGrowth65.prod
  intro i hi
  exact (logGrowth65_const _).mul ((hμ i).neg.pow _)

end Luce.Section6
