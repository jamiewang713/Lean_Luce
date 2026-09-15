import Luce.Section3Poisson
import Luce.Section4Fatou

/-! # Expectation lower bounds from the already proved interior compensator

Source: `fixed_points.tex:936–945`. This supplies the lower-semicontinuity
argument using the actual predictable compensator and its conditional-mean
identity. It does not assume convergence of unbounded expectations.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace Luce

/-- Integrating a finite conditional probability recovers the observation's
expectation; clipping the conditional expectation changes only a null set. -/
theorem FiniteAdaptedBernoulli.integral_probability_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (B : FiniteAdaptedBernoulli P n) (k : Fin n) :
    (∫ ω, B.probability k ω ∂P) = ∫ ω, B.observationReal k ω ∂P := by
  rw [integral_congr_ae (B.probability_ae_eq_condExp k)]
  exact integral_condExp (B.filtration.le k.val)

/-- Spatially weighted observed and predictable measures have identical
expectations, with integrability supplied by the finite row. -/
theorem FiniteAdaptedBernoulli.integral_predictable_eq_observed
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    (B : FiniteAdaptedBernoulli P n) (x : Fin n → X) (g : X → ℝ)
    (hg : Measurable g) :
    (∫ ω, ∫ y, g y ∂(B.predictableMeasure x ω : Measure X) ∂P) =
      ∫ ω, ∫ y, g y ∂((B.pointMeasure x ω).toFiniteMeasure : Measure X) ∂P := by
  simp_rw [B.integral_predictableMeasure x g hg]
  have ho (ω : Ω) :
      (∫ y, g y ∂((B.pointMeasure x ω).toFiniteMeasure : Measure X)) =
        ∑ k, B.observationReal k ω * g (x k) :=
    integral_observedPointMeasure x (fun k => B.observation k ω) g hg
  simp_rw [ho]
  rw [integral_finsetSum _ (fun k _ => (B.integrable_probability k).mul_const (g (x k))),
    integral_finsetSum _ (fun k _ => (B.integrable_observationReal k).mul_const (g (x k)))]
  simp_rw [integral_mul_const, B.integral_probability_eq]

/-- The limiting intensity of a nonnegative continuous test is bounded by
the limsup of its actual observed expectations. Only the upper boundedness
needed for a real limsup is assumed here; endpoint estimates discharge it
when the test is supported in the terminal interval. -/
theorem section4_interior_test_expectation_lower
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) (hg : ∀ x, 0 ≤ g x)
    (hbounded : IsBoundedUnder (· ≤ ·) atTop (fun n => ∫ e,
      ∫ y, g y ∂((interiorFixedPoints α (raceDraw e)).toFiniteMeasure :
        Measure (Icc (0 : ℝ) 1)) ∂exponentialRace (w n))) :
    (∫ y, g y ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1))) ≤
      limsup (fun n => ∫ e, ∫ y, g y
        ∂((interiorFixedPoints α (raceDraw e)).toFiniteMeasure : Measure (Icc (0 : ℝ) 1))
        ∂exponentialRace (w n)) atTop := by
  let B := fun n => raceInteriorBernoulli (w n) α
  let X := fun n e => ∫ y, g y ∂((B n).predictableMeasure (section3Location n) e :
    Measure (Icc (0 : ℝ) 1))
  have hx (n : ℕ) (e : Fin n → ℝ) : X n e =
      ∑ k, (B n).probability k e * g (section3Location n k) :=
    (B n).integral_predictableMeasure _ _ g.continuous.measurable e
  have hmeas (n : ℕ) : Measurable (X n) := by
    simp_rw [show X n = fun e => ∑ k, (B n).probability k e * g (section3Location n k)
      from funext (hx n)]
    exact Finset.measurable_sum _ (fun k _ =>
      (((B n).probability_predictable k).mono ((B n).filtration.le k.val)).measurable.mul_const _)
  have hint (n : ℕ) : Integrable (X n) (exponentialRace (w n)) := by
    simp_rw [show X n = fun e => ∑ k, (B n).probability k e * g (section3Location n k)
      from funext (hx n)]
    exact integrable_finsetSum _ (fun k _ => ((B n).integrable_probability k).mul_const _)
  have heq (n : ℕ) : (∫ e, X n e ∂exponentialRace (w n)) =
      ∫ e, ∫ y, g y ∂((interiorFixedPoints α (raceDraw e)).toFiniteMeasure :
        Measure (Icc (0 : ℝ) 1)) ∂exponentialRace (w n) := by
    have h := (B n).integral_predictable_eq_observed (section3Location n) g g.continuous.measurable
    simpa only [B, raceInteriorBernoulli_pointMeasure] using h
  have hbound : IsBoundedUnder (· ≤ ·) atTop
      (fun n => ∫ e, X n e ∂exponentialRace (w n)) := by
    simpa only [heq] using hbounded
  have hconv : ConvergesInProbability (fun n => exponentialRace (w n)) X
      (∫ y, g y ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1))) :=
    section3_predictable_tests w f hnorm hf hα g
  have h := hconv.le_limsup_integral
    hmeas hint (fun _ _ => integral_nonneg hg)
    (integral_nonneg hg) hbound
  simpa only [heq] using h

end Luce
