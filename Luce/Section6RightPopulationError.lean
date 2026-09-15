import Luce.Section6RightPopulationComparison

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The actual right-endpoint survivor population with its exact Gamma
leading term. Every error constant is derived from the sampled profile.
The explicit bound precedes reduction to the manuscript's relative-O form. -/
theorem PowerProfile.right_populationH_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ C d eps : ℝ, 0 < C ∧ 0 < d ∧ 0 < eps ∧ eps < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t →
    |populationH (w n) t - (1/(c*t))^(1/beta)*Real.Gamma (1+1/beta)| ≤
      C*t*(1/(c*t/4))^((beta+eta)/beta)*
        ((1/(c*t/4))^(1/beta)*Real.Gamma (1+1/beta) + 1/(n : ℝ)) +
      survivalKernel t d + survivalKernel t (c*eps^beta) + 1/(n : ℝ) +
      Real.exp (-(c*t)/2)*((1/((c*t)/2))^(1/beta)*Real.Gamma (1+1/beta)) := by
  obtain ⟨C, d, eps, hC, hd, heps, heps1, hcomp⟩ := h.right_populationH_comparison
  refine ⟨C, d, eps, hC, hd, heps, heps1, ?_⟩
  intro grid w hw n hn t ht
  have hp := slow_prototype_population_error grid hn h.2.2.2.1.2.1
    (mul_pos h.2.2.2.1.1 ht)
  have hc := hcomp grid w hw n hn t ht
  calc
    _ ≤ |populationH (w n) t -
        (∑ i : Fin n, Real.exp (-((c*t)*(samplePoint grid n i)^beta)))/(n : ℝ)| +
        |(∑ i : Fin n, Real.exp (-((c*t)*(samplePoint grid n i)^beta)))/(n : ℝ) -
          (1/(c*t))^(1/beta)*Real.Gamma (1+1/beta)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hc hp
    _ = _ := by ring

end Luce.Section6
