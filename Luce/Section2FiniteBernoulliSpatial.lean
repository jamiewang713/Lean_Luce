import Luce.Section2BernoulliPointMeasure
import Luce.Section2FiniteAdaptedBernoulli
import Luce.Section2FiniteBernoulliRow
import Luce.Section2CappedPoisson

/-!
# Spatial measures associated with finite adapted Bernoulli rows

The point and predictable measures are the literal finite sums of Dirac
measures. Their scalar tests agree with the zero-extended finite rows used
in the likelihood argument, including for empty rows and empty spatial spaces.
-/

open MeasureTheory
open scoped BigOperators NNReal

namespace Luce

variable {X : Type*} [MeasurableSpace X]

/-- Fixed finite locations give a continuous map from nonnegative weights
to finite measures with their weak topology. -/
theorem continuous_weightedPointMeasure [TopologicalSpace X] [OpensMeasurableSpace X]
    {n : ℕ} (x : Fin n → X) : Continuous (weightedPointMeasure x) := by
  unfold weightedPointMeasure
  exact continuous_finsetSum _ (fun k _ => (continuous_apply k).smul continuous_const)

namespace FiniteAdaptedBernoulli

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {n : ℕ}
    (B : FiniteAdaptedBernoulli P n)

/-- The observed finite point measure for the finite row. -/
noncomputable def pointMeasure (x : Fin n → X) (ω : Ω) : FinitePointMeasure X :=
  observedPointMeasure x (fun k => B.observation k ω)

/-- The predictable measure, using the canonical nonnegative version of
the conditional probabilities already supplied by the row adapter. -/
noncomputable def predictableMeasure (x : Fin n → X) (ω : Ω) : FiniteMeasure X :=
  weightedPointMeasure x (fun k =>
    (⟨B.probability k ω, B.probability_nonneg k ω⟩ : ℝ≥0))

theorem measurable_pointMeasure (x : Fin n → X) : Measurable (B.pointMeasure x) := by
  exact measurable_observedPointMeasure_of_measurable x B.observation
    (fun k => (B.adapted k).mono (B.filtration.le (k.val + 1)) le_rfl)

theorem measurable_predictableMeasure (x : Fin n → X) :
    Measurable (B.predictableMeasure x) := by
  apply measurable_weightedPointMeasure_of_measurable
  intro k
  exact ((B.probability_predictable k).mono (B.filtration.le k.val)).measurable.subtype_mk

/-- Weak-open preimages are measurable directly through the finite
coefficient vector. No Borel compatibility for the space of finite
measures is assumed. -/
theorem measurableSet_predictableMeasure_preimage [TopologicalSpace X]
    [OpensMeasurableSpace X] (x : Fin n → X) {U : Set (FiniteMeasure X)}
    (hU : IsOpen U) : MeasurableSet {ω | B.predictableMeasure x ω ∈ U} := by
  have hp : Measurable (fun ω => fun k : Fin n =>
      (⟨B.probability k ω, B.probability_nonneg k ω⟩ : ℝ≥0)) :=
    measurable_pi_lambda _ (fun k =>
      ((B.probability_predictable k).mono (B.filtration.le k.val)).measurable.subtype_mk)
  exact ((hU.preimage (continuous_weightedPointMeasure x)).measurableSet).preimage hp

theorem integral_predictableMeasure (x : Fin n → X) (g : X → ℝ)
    (hg : Measurable g) (ω : Ω) :
    (∫ y, g y ∂(B.predictableMeasure x ω : Measure X)) =
      ∑ k, B.probability k ω * g (x k) :=
  integral_weightedPointMeasure x _ g hg

/-- Extend a spatial test by zero outside its finite row. -/
def spatialTest (x : Fin n → X) (g : X → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then g (x ⟨k, h⟩) else 0

omit [MeasurableSpace X] in
@[simp] theorem spatialTest_at_fin (x : Fin n → X) (g : X → ℝ) (k : Fin n) :
    spatialTest x g k.val = g (x k) := by
  simp [spatialTest, k.isLt]

omit [MeasurableSpace X] in
theorem spatialTest_nonneg (x : Fin n → X) (g : X → ℝ)
    (hg : ∀ y, 0 ≤ g y) (k : ℕ) : 0 ≤ spatialTest x g k := by
  unfold spatialTest
  split_ifs
  · exact hg _
  · exact le_rfl

variable [IsProbabilityMeasure P]

theorem pointMeasure_mass (x : Fin n → X) (ω : Ω) :
    ((B.pointMeasure x ω).toFiniteMeasure.mass : ℝ) =
      ∑ k ∈ Finset.range n, B.toProcess.observation k ω := by
  rw [pointMeasure, observedPointMeasure_mass, NNReal.coe_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp only [B.toProcess_observation, observationReal]
  split_ifs <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem predictableMeasure_mass (x : Fin n → X) (ω : Ω) :
    ((B.predictableMeasure x ω).mass : ℝ) =
      ∑ k ∈ Finset.range n, B.toProcess.probability k ω := by
  calc
    ((B.predictableMeasure x ω).mass : ℝ) =
        (((∑ k, (⟨B.probability k ω, B.probability_nonneg k ω⟩ : ℝ≥0)) : ℝ≥0) : ℝ) :=
      congrArg (fun a : ℝ≥0 => (a : ℝ)) (weightedPointMeasure_mass x
        (fun k => (⟨B.probability k ω, B.probability_nonneg k ω⟩ : ℝ≥0)))
    _ = ∑ k ∈ Finset.range n, B.toProcess.probability k ω := by
      rw [NNReal.coe_sum, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _
      exact (congrFun (B.toProcess_probability k) ω).symm

theorem pointLaplace_pointMeasure (x : Fin n → X) (g : X → ℝ)
    (hg : Measurable g) (ω : Ω) :
    pointLaplace g (B.pointMeasure x ω) =
      Real.exp (-(∑ k ∈ Finset.range n,
        spatialTest x g k * B.toProcess.observation k ω)) := by
  rw [pointMeasure, pointLaplace_observedPointMeasure x _ g hg]
  rw [← Fin.sum_univ_eq_sum_range]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  simp only [spatialTest_at_fin, B.toProcess_observation, observationReal]
  exact mul_comm _ _

theorem laplaceCompensator_eq_integral_predictableMeasure (x : Fin n → X)
    (g : X → ℝ) (hg : Measurable g) (ω : Ω) :
    B.toProcess.laplaceCompensator (spatialTest x g) n ω =
      ∫ y, 1 - Real.exp (-g y) ∂(B.predictableMeasure x ω : Measure X) := by
  rw [B.integral_predictableMeasure x (fun y => 1 - Real.exp (-g y))
    (measurable_const.sub hg.neg.exp) ω]
  unfold BernoulliProcess.laplaceCompensator
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp

end FiniteAdaptedBernoulli
end Luce
