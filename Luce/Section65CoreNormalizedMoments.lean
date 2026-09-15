import Luce.Section65CoreCenteredMoments
import Luce.Section65PoissonMomentLimit
import Mathlib.Analysis.Real.Sqrt

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Luce.Section6

def normalizedCoreCategory65 (left right : EndpointBehavior) {n : ℕ}
    (R : Equiv.Perm (Fin n)) (c : CoreCycleCategory) : ℝ :=
  ((coreCategoryCount R c : ℝ)-coreCategoryIdealMean left right n c) /
    Real.sqrt (coreCategoryIdealMean left right n c)

theorem core_normalized_mixed_moments65
    (f : ℝ → ℝ) (left right : EndpointBehavior) (hp : PowerProfile f left right)
    (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (q : ℕ) (c : Fin q → CoreCycleCategory)
    (ha : ∀ i, (cornerBehavior left right (c i).side).active)
    (hd : CoreCategoriesDisjoint c)
    (hg : ∀ i, LogGrowth65 (fun n => coreCategoryIdealMean left right n (c i)))
    (ht : ∀ i, Tendsto (fun n => coreCategoryIdealMean left right n (c i)) atTop atTop)
    (r : Fin q → ℕ) :
    Tendsto (fun n => ∫ clocks, ∏ i : Fin q,
      (normalizedCoreCategory65 left right (raceRankPermutation clocks) (c i))^(r i)
        ∂exponentialRace (w n)) atTop (𝓝 (∏ i, gaussianMoment65 1 (r i))) := by
  classical
  let μ (n : ℕ) (i : Fin q) := coreCategoryIdealMean left right n (c i)
  let b (n : ℕ) (i : Fin q) := Real.sqrt (μ n i)
  let a (n : ℕ) : ℝ := ∏ i : Fin q, (b n i^(r i))⁻¹
  let E (n : ℕ) : ℝ := (∫ clocks, ∏ i : Fin q,
    ((coreCategoryCount (raceRankPermutation clocks) (c i) : ℝ)-μ n i)^(r i)
      ∂exponentialRace (w n)) - ∏ i, centeredPoissonMoment65 (μ n i) (r i)
  have hb (i : Fin q) : Tendsto (fun n => b n i) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (ht i)
  have hga : LogGrowth65 a := by
    apply LogGrowth65.prod
    intro i hi
    refine ⟨1,zero_lt_one,0,?_⟩
    filter_upwards [(hb i).eventually_ge_atTop 1] with n hn
    have hpow : 1 ≤ b n i^(r i) := one_le_pow₀ hn
    rw [abs_of_nonneg (inv_nonneg.mpr (le_trans zero_le_one hpow))]
    simpa using inv_le_one_of_one_le₀ hpow
  have hE : RapidError65 E := core_centered_moment_rapid65 f left right hp grid w hs q c ha hd hg r
  let Q (n : ℕ) : ℝ := ∏ i : Fin q, centeredPoissonMoment65 (μ n i) (r i) / b n i^(r i)
  have hQ : Tendsto Q atTop (𝓝 (∏ i, gaussianMoment65 1 (r i))) := by
    apply tendsto_finsetProd
    intro i hi
    have h := scaledPoissonMoment65_tendsto (fun n => b n i) (hb i) (r i)
    apply h.congr'
    filter_upwards [(ht i).eventually_ge_atTop 0] with n hn
    simp only [scaledPoissonMoment65, b, μ, Real.sq_sqrt hn]
  have he (n : ℕ) :
      (∫ clocks, ∏ i : Fin q,
        (normalizedCoreCategory65 left right (raceRankPermutation clocks) (c i))^(r i)
          ∂exponentialRace (w n)) = a n*E n+Q n := by
    simp only [normalizedCoreCategory65, div_pow, Finset.prod_div_distrib]
    rw [integral_div]
    dsimp [a,E,Q,b,μ]
    rw [Finset.prod_inv_distrib, Finset.prod_div_distrib]
    ring
  simp_rw [he]
  simpa using (hE.mul_growth hga).tendsto.add hQ

end Luce.Section6
