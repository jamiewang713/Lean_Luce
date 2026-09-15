import Luce.Section6CriticalPopulationComparison
import Luce.Section6CriticalPoleIntegrals

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

/-- Explicit critical population estimates, derived from the literal
profile hypotheses and valid for both sampling grids. -/
theorem CriticalProfile.population_estimates {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (grid : SamplingGrid) (w : WeightArray),
      SampledRates grid w f → ∀ (n : ℕ), 0 < n → ∀ t : ℝ, 0 < t → t ≤ 1 →
      |populationG (w n) t-(c*t)*Real.log (1/t)| ≤ C*t+1/(n : ℝ) ∧
      |populationD (w n) 1 t-c*Real.log (1/t)| ≤ C+2*Real.exp (-1)/((n : ℝ)*t) := by
  obtain ⟨C,hC,hcomp⟩ := hp.population_pole_comparison
  have hc : 0 < c := hp.2.2.1
  refine ⟨C+1+c^2+Real.exp (-1),by positivity,?_⟩
  intro grid w hw n hn t ht ht1
  obtain ⟨hG,hD⟩ := hcomp grid w hw n hn t ht.le
  have hqG : |(∑ i : Fin n, (1-survivalKernel t (c/samplePoint grid n i)))/n -
      ∫ s in (0 : ℝ)..1, 1-survivalKernel t (c/s)| ≤ 1/(n : ℝ) := by
    simpa only [survivalKernel,Real.rpow_neg_one,neg_mul,mul_neg,div_eq_mul_inv,
      mul_comm,mul_left_comm,mul_assoc] using
      fast_arrival_quadrature grid hn (alpha := 1) (r := c*t) zero_lt_one (mul_pos hc ht)
  have hqD : |(∑ i : Fin n, rateKernel t (c/samplePoint grid n i))/n -
      ∫ s in (0 : ℝ)..1, rateKernel t (c/s)| ≤ (2*(Real.exp (-1)/t))/(n : ℝ) := by
    simpa only [Real.rpow_neg_one,div_eq_mul_inv] using
      fast_weighted_quadrature grid hn (alpha := 1) zero_lt_one hc ht
  constructor
  · calc
      _ ≤ |populationG (w n) t -
          (∑ i : Fin n, (1-survivalKernel t (c/samplePoint grid n i)))/n| +
          |(∑ i : Fin n, (1-survivalKernel t (c/samplePoint grid n i)))/n-
            (c*t)*Real.log (1/t)| := abs_sub_le _ _ _
      _ ≤ C*t+(1/n+(1+c^2)*t) := add_le_add hG
        ((abs_sub_le _ (∫ s in (0 : ℝ)..1, 1-survivalKernel t (c/s)) _).trans
          (add_le_add hqG (critical_pole_arrival_integral hc ht ht1)))
      _ ≤ _ := by nlinarith [mul_pos (Real.exp_pos (-1)) ht]
  · calc
      _ ≤ |populationD (w n) 1 t -
          (∑ i : Fin n, rateKernel t (c/samplePoint grid n i))/n| +
          |(∑ i : Fin n, rateKernel t (c/samplePoint grid n i))/n-c*Real.log (1/t)| := abs_sub_le _ _ _
      _ ≤ C+((2*(Real.exp (-1)/t))/n+(Real.exp (-1)+c^2)) := add_le_add hD
        ((abs_sub_le _ (∫ s in (0 : ℝ)..1, rateKernel t (c/s)) _).trans
          (add_le_add hqD (critical_pole_weight_integral hc ht ht1)))
      _ ≤ _ := by ring_nf; linarith

end Luce.Section6
