import Luce.Section65RapidError
import Luce.Section65PolynomialExpansion
import Luce.Section6Proposition610
import Luce.Section5FiniteStatistic

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

theorem core_factorial_rapid65 (r : Fin q → ℕ) :
    RapidError65 (fun n => (∫ clocks, ∏ i : Fin q,
      ((coreCategoryCount (raceRankPermutation clocks) (c i)).descFactorial (r i) : ℝ)
        ∂exponentialRace (w n)) - ∏ i, (coreCategoryIdealMean left right n (c i))^(r i)) := by
  obtain ⟨C,κ,hC,hκ,K,N,hN,h⟩ := proposition610 f left right hp grid w hs q c ha hd r
  apply rapidError65_of_core_bound hκ
  exact eventually_atTop.mpr ⟨N, fun n hn => h n hn⟩

theorem core_polynomial_rapid65 (p : Fin q → ℝ[X]) :
    RapidError65 (fun n => (∫ clocks, ∏ i : Fin q,
      (p i).eval (coreCategoryCount (raceRankPermutation clocks) (c i) : ℝ)
        ∂exponentialRace (w n)) -
      ∏ i, poissonFunctional65 (coreCategoryIdealMean left right n (c i)) (p i)) := by
  classical
  let V := (i : Fin q) → ↥(fallingSupport65 (p i))
  let a (v : V) : ℝ := ∏ i, fallingCoeff65 (p i) (v i)
  let r (v : V) : Fin q → ℕ := fun i => (v i).val
  let e (v : V) (n : ℕ) : ℝ :=
    (∫ clocks, ∏ i : Fin q,
      ((coreCategoryCount (raceRankPermutation clocks) (c i)).descFactorial (r v i) : ℝ)
        ∂exponentialRace (w n)) - ∏ i, (coreCategoryIdealMean left right n (c i))^(r v i)
  have hex (i : Fin q) (x : ℕ) : (p i).eval (x : ℝ) =
      ∑ j : ↥(fallingSupport65 (p i)), fallingCoeff65 (p i) j * (x.descFactorial j.val : ℝ) := by
    rw [polynomial_eval_expansion65]
    simp only [descPochhammer_eval_eq_descFactorial]
  have he (n : ℕ) : (∫ clocks, ∏ i : Fin q,
      (p i).eval (coreCategoryCount (raceRankPermutation clocks) (c i) : ℝ)
        ∂exponentialRace (w n)) -
      ∏ i, poissonFunctional65 (coreCategoryIdealMean left right n (c i)) (p i) =
        ∑ v : V, a v*e v n := by
    simp_rw [hex,
      poissonFunctional65_expansion, Fintype.prod_sum, Finset.prod_mul_distrib]
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      dsimp [a,e,r]
      ring
    · intro v hv
      exact integrable_race_permutation_statistic (w n) (fun R =>
        (∏ i, fallingCoeff65 (p i) (v i)) * ∏ i : Fin q,
          ((coreCategoryCount R (c i)).descFactorial (v i).val : ℝ))
  simp_rw [he]
  apply RapidError65.sum
  intro v hv
  exact (core_factorial_rapid65 f left right hp grid w hs q c ha hd (r v)).const_mul (a v)

end Luce.Section6
