import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

/-! # Mixing probability laws with a Poisson count

This generic construction is an ingredient of the finite Poisson random
measure used in `lem:predictable-poisson`. The measurable state space is
arbitrary. Its Laplace computation alone is not a characterization of a
Poisson random measure.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Nat

namespace Luce

/-- A probability mixture whose component index has the scalar Poisson law. -/
noncomputable def poissonMixture {E : Type*} [MeasurableSpace E]
    (r : ℝ≥0) (Q : ℕ → Measure E) : Measure E :=
  (poissonMeasure r).bind Q

instance poissonMixture_isProbabilityMeasure {E : Type*} [MeasurableSpace E]
    (r : ℝ≥0) (Q : ℕ → Measure E) [∀ m, IsProbabilityMeasure (Q m)] :
    IsProbabilityMeasure (poissonMixture r Q) :=
  isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

private lemma integrable_of_zero_le_le_one {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (F : E → ℝ)
    (hF : Measurable F) (hF01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    Integrable F μ := by
  apply (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF01 x).1] using (hF01 x).2

/-- The scalar Poisson probability-generating function on `[0,1]`, including
zero rate and zero argument. Integrability is established before using the
Poisson-series integral formula. -/
theorem integral_pow_poissonMeasure (r : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ m : ℕ, a ^ m ∂poissonMeasure r) = Real.exp (-(r : ℝ) * (1 - a)) := by
  have hint : Integrable (fun m : ℕ => a ^ m) (poissonMeasure r) :=
    integrable_of_zero_le_le_one (poissonMeasure r) _ Measurable.of_discrete
      (fun _ => ⟨pow_nonneg ha _, pow_le_one₀ ha ha1⟩)
  have hseries :=
    (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * a)).mul_left (Real.exp (-(r : ℝ)))
  rw [← Real.exp_eq_exp_ℝ] at hseries
  calc
    _ = ∑' m : ℕ, (Real.exp (-(r : ℝ)) * (r : ℝ) ^ m / (m)!) * a ^ m := by
      simpa only [smul_eq_mul] using integral_poissonMeasure' hint
    _ = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * a) := by
      convert hseries.tsum_eq using 1
      apply tsum_congr
      intro m
      rw [mul_pow]
      ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- A bounded measurable test is integrable under the Poisson mixture. -/
theorem integrable_poissonMixture {E : Type*} [MeasurableSpace E]
    (r : ℝ≥0) (Q : ℕ → Measure E) [∀ m, IsProbabilityMeasure (Q m)]
    (F : E → ℝ) (hF : Measurable F) (hF01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    Integrable F (poissonMixture r Q) :=
  integrable_of_zero_le_le_one _ F hF hF01

/-- If the test integral in the component with `m` points is `a ^ m`,
mixing those components with a Poisson count gives the required exponential
formula. No nonempty state-space or positive-rate hypothesis is imposed. -/
theorem integral_poissonMixture_of_power {E : Type*} [MeasurableSpace E]
    (r : ℝ≥0) (Q : ℕ → Measure E) [∀ m, IsProbabilityMeasure (Q m)]
    (F : E → ℝ) (hF : Measurable F) (hF01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomponent : ∀ m : ℕ, (∫ x, F x ∂Q m) = a ^ m) :
    (∫ x, F x ∂poissonMixture r Q) = Real.exp (-(r : ℝ) * (1 - a)) := by
  have hFnonneg (μ : Measure E) : 0 ≤ᵐ[μ] F :=
    Eventually.of_forall fun x => (hF01 x).1
  have hcomponentNN (m : ℕ) :
      (∫⁻ x, ENNReal.ofReal (F x) ∂Q m) = ENNReal.ofReal (a ^ m) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_of_zero_le_le_one (Q m) F hF hF01) (hFnonneg _), hcomponent]
  calc
    _ = (∫⁻ x, ENNReal.ofReal (F x) ∂poissonMixture r Q).toReal := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrable_poissonMixture r Q F hF hF01) (hFnonneg _),
        ENNReal.toReal_ofReal (integral_nonneg fun x => (hF01 x).1)]
    _ = (∫⁻ m : ℕ, ENNReal.ofReal (a ^ m) ∂poissonMeasure r).toReal := by
      rw [poissonMixture,
        Measure.lintegral_bind Measurable.of_discrete.aemeasurable hF.ennreal_ofReal.aemeasurable]
      simp only [hcomponentNN]
    _ = ∫ m : ℕ, a ^ m ∂poissonMeasure r :=
      (integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun m => pow_nonneg ha m)
        Measurable.of_discrete.aestronglyMeasurable).symm
    _ = _ := integral_pow_poissonMeasure r ha ha1

end Luce
