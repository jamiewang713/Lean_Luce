import Luce.BernoulliProcess

/-!
# Uniform second moments for the predictable likelihood

This proves the bound in `fixed_points.tex`, `eq:likelihood-L2`, with
`Cδ = 1 / (1 - δ)`. The existing deterministic cap gives `0 ≤ L ≤ C`,
where `C = exp (K / (1 - δ))`. Thus `L² ≤ C * L`; integrating and using
the already proved mean-one identity gives `E[L²] ≤ C`.

In particular no random predictable probability is pulled out of an
unconditional expectation during an iteration of second moments.
-/

open MeasureTheory
open scoped BigOperators

namespace Luce.BernoulliProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] (X : BernoulliProcess μ)

private lemma likelihood_bounds_of_terminal_cap {δ K : ℝ} (hδ : δ < 1)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ)
    (hK : ∀ ω, ∑ k ∈ Finset.range N, X.probability k ω ≤ K)
    {m : ℕ} (hm : m ≤ N) (ω : Ω) :
    0 ≤ X.likelihood g m ω ∧
      X.likelihood g m ω ≤ Real.exp (K / (1 - δ)) := by
  apply X.likelihood_bounds_of_sum_le hδ g hg hpδ m ω
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
    (fun k _ _ => X.probability_nonneg k ω)).trans (hK ω)

/-- The capped likelihood has an integrable square at every prefix. -/
theorem integrable_likelihood_sq {δ K : ℝ} (hδ : δ < 1)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ)
    (hK : ∀ ω, ∑ k ∈ Finset.range N, X.probability k ω ≤ K)
    {m : ℕ} (hm : m ≤ N) :
    Integrable (fun ω => (X.likelihood g m ω) ^ 2) μ := by
  have hL := X.likelihood_integrable hδ g hg hpδ m
  have hbound : ∀ᵐ ω ∂μ, ‖X.likelihood g m ω‖ ≤ Real.exp (K / (1 - δ)) := by
    apply ae_of_all
    intro ω
    have hb := X.likelihood_bounds_of_terminal_cap hδ g hg hpδ N hK hm ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  simpa only [pow_two] using hL.mul_bdd hL.aestronglyMeasurable hbound

/-- Uniform second-moment estimate in the manuscript's form
`E[L_m²] ≤ exp(Cδ * K)`, with `Cδ = 1 / (1 - δ)`.
The decisive estimate is the pointwise `L_m² ≤ exp(K/(1-δ)) * L_m`,
followed by the mean-one identity. -/
theorem integral_likelihood_sq_le {δ K : ℝ} (hδ : δ < 1)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ)
    (hK : ∀ ω, ∑ k ∈ Finset.range N, X.probability k ω ≤ K)
    {m : ℕ} (hm : m ≤ N) :
    (∫ ω, (X.likelihood g m ω) ^ 2 ∂μ) ≤ Real.exp (K / (1 - δ)) := by
  have hL := X.likelihood_integrable hδ g hg hpδ m
  calc
    (∫ ω, (X.likelihood g m ω) ^ 2 ∂μ) ≤
        ∫ ω, Real.exp (K / (1 - δ)) * X.likelihood g m ω ∂μ := by
      apply integral_mono (X.integrable_likelihood_sq hδ g hg hpδ N hK hm)
        (hL.const_mul _)
      intro ω
      have hb := X.likelihood_bounds_of_terminal_cap hδ g hg hpδ N hK hm ω
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hb.2 hb.1
    _ = Real.exp (K / (1 - δ)) := by
      rw [integral_const_mul, X.integral_likelihood hδ g hg hpδ m, mul_one]

/-- The manuscript's predictable deletion construction supplies the caps,
so the second-moment bound is uniform over every time of a stopped row. -/
theorem stopped_integral_likelihood_sq_le {δ K : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) (hK : 0 ≤ K) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (m : ℕ) :
    (∫ ω, ((X.stop δ K).likelihood g m ω) ^ 2 ∂μ) ≤
      Real.exp (K / (1 - δ)) := by
  exact (X.stop δ K).integral_likelihood_sq_le hδ g hg
    (fun k ω => X.stop_probability_le_cap hδ0 k ω) m
    (fun ω => X.stop_sum_probability_le_cap hK m ω) le_rfl

end Luce.BernoulliProcess
