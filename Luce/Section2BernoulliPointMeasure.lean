import Luce.Section2FinitePointMeasure
import Luce.Section2FinitePoissonLaw
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite Bernoulli arrays as actual point measures

These definitions and identities connect the finite arrays in
`lem:predictable-poisson` with the actual observed and predictable measures.
The spatial space need only be measurable; no separation, nonemptiness,
or measurable-singleton assumption is imposed on it.
-/

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Luce

variable {X : Type*} [MeasurableSpace X]

/-- Retain exactly the points with true Bernoulli observations. The finite
enumeration certifies that the resulting measure is a finite point measure. -/
noncomputable def observedPointMeasure {n : ℕ} (x : Fin n → X)
    (b : Fin n → Bool) : FinitePointMeasure X :=
  let s := Finset.univ.filter (fun k => b k)
  FinitePointMeasure.ofFin (fun j : Fin s.card => x (s.equivFin.symm j))

private lemma sum_selected_enumeration {n : ℕ} {A : Type*} [AddCommMonoid A]
    (b : Fin n → Bool) (f : Fin n → A) :
    (let s := Finset.univ.filter (fun k => b k)
     ∑ j : Fin s.card, f (s.equivFin.symm j)) = ∑ k, if b k then f k else 0 := by
  classical
  let s := Finset.univ.filter (fun k => b k)
  change (∑ j : Fin s.card, f (s.equivFin.symm j)) = _
  rw [Equiv.sum_comp s.equivFin.symm (fun j : s => f j), Finset.sum_coe_sort]
  exact Finset.sum_filter _ _

/-- The underlying measure is the literal sum of retained unit Dirac masses. -/
theorem observedPointMeasure_toFiniteMeasure {n : ℕ} (x : Fin n → X)
    (b : Fin n → Bool) :
    (observedPointMeasure x b).toFiniteMeasure =
      ∑ k, if b k then (diracProba (x k)).toFiniteMeasure else 0 := by
  exact sum_selected_enumeration b (fun k => (diracProba (x k)).toFiniteMeasure)

private lemma mass_sum_for_bernoulli {A : Type*} (s : Finset A) (μ : A → FiniteMeasure X) :
    (∑ i ∈ s, μ i).mass = ∑ i ∈ s, (μ i).mass := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    calc
      (μ i + ∑ j ∈ s, μ j).mass = (μ i).mass + (∑ j ∈ s, μ j).mass := by
        simp [FiniteMeasure.mass, FiniteMeasure.coeFn_add]
      _ = _ := by rw [ih]

/-- The total mass is the number of true observations, including when
several observations occur at the same spatial point. -/
theorem observedPointMeasure_mass {n : ℕ} (x : Fin n → X) (b : Fin n → Bool) :
    (observedPointMeasure x b).toFiniteMeasure.mass =
      ∑ k, if b k then (1 : ℝ≥0) else 0 := by
  rw [observedPointMeasure_toFiniteMeasure, mass_sum_for_bernoulli]
  apply Finset.sum_congr rfl
  intro k _
  cases b k <;> simp

/-- Spatial integration agrees with the literal Bernoulli-weighted sum. -/
theorem integral_observedPointMeasure {n : ℕ} (x : Fin n → X) (b : Fin n → Bool)
    (g : X → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂((observedPointMeasure x b).toFiniteMeasure : Measure X)) =
      ∑ k, (if b k then (1 : ℝ) else 0) * g (x k) := by
  unfold observedPointMeasure
  rw [FinitePointMeasure.toFiniteMeasure_ofFin, integral_pointMeasureOfFin _ g hg]
  rw [sum_selected_enumeration b (fun k => g (x k))]
  apply Finset.sum_congr rfl
  intro k _
  cases b k <;> simp

/-- The point-measure Laplace test is exactly the exponential used in the
finite-row likelihood argument. -/
theorem pointLaplace_observedPointMeasure {n : ℕ} (x : Fin n → X) (b : Fin n → Bool)
    (g : X → ℝ) (hg : Measurable g) :
    pointLaplace g (observedPointMeasure x b) =
      Real.exp (-(∑ k, (if b k then (1 : ℝ) else 0) * g (x k))) := by
  rw [pointLaplace, integral_observedPointMeasure x b g hg]

theorem measurable_observedPointMeasure {n : ℕ} (x : Fin n → X) :
    Measurable (observedPointMeasure x) := measurable_of_finite _

/-- Coordinate-measurable Bernoulli observations give an actual measurable
random point measure, with no extra regularity imposed on the sample space. -/
theorem measurable_observedPointMeasure_of_measurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → X)
    (I : Fin n → Ω → Bool) (hI : ∀ k, Measurable (I k)) :
    Measurable (fun ω => observedPointMeasure x (fun k => I k ω)) :=
  (measurable_observedPointMeasure x).comp (measurable_pi_lambda _ hI)

/-- The literal finite predictable measure with nonnegative coefficients. -/
noncomputable def weightedPointMeasure {n : ℕ} (x : Fin n → X)
    (p : Fin n → ℝ≥0) : FiniteMeasure X :=
  ∑ k, p k • (diracProba (x k)).toFiniteMeasure

theorem weightedPointMeasure_mass {n : ℕ} (x : Fin n → X) (p : Fin n → ℝ≥0) :
    (weightedPointMeasure x p).mass = ∑ k, p k := by
  rw [weightedPointMeasure, mass_sum_for_bernoulli]
  apply Finset.sum_congr rfl
  intro k _
  simp [FiniteMeasure.mass, FiniteMeasure.smul_apply]

theorem integrable_weightedPointMeasure {n : ℕ} (x : Fin n → X) (p : Fin n → ℝ≥0)
    (g : X → ℝ) (hg : Measurable g) :
    Integrable g (weightedPointMeasure x p : Measure X) := by
  simp only [weightedPointMeasure, FiniteMeasure.toMeasure_sum, FiniteMeasure.toMeasure_smul]
  change Integrable g (∑ k, p k • Measure.dirac (x k))
  exact integrable_finsetSum_measure.mpr fun k _ =>
    (integrable_dirac' hg.stronglyMeasurable (by simp)).smul_measure_nnreal

theorem integral_weightedPointMeasure {n : ℕ} (x : Fin n → X) (p : Fin n → ℝ≥0)
    (g : X → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂(weightedPointMeasure x p : Measure X)) =
      ∑ k, (p k : ℝ) * g (x k) := by
  simp only [weightedPointMeasure, FiniteMeasure.toMeasure_sum, FiniteMeasure.toMeasure_smul]
  change (∫ y, g y ∂(∑ k, p k • Measure.dirac (x k))) = _
  rw [integral_finsetSum_measure (fun k _ =>
    (integrable_dirac' hg.stronglyMeasurable (by simp)).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure, integral_dirac' _ _ hg.stronglyMeasurable,
    NNReal.smul_def, smul_eq_mul]

theorem measurable_weightedPointMeasure {n : ℕ} (x : Fin n → X) :
    Measurable (weightedPointMeasure x) := by
  apply Measurable.subtype_mk
  change Measurable (fun p : Fin n → ℝ≥0 =>
    ((weightedPointMeasure x p : FiniteMeasure X) : Measure X))
  simp only [weightedPointMeasure, FiniteMeasure.toMeasure_sum, FiniteMeasure.toMeasure_smul]
  change Measurable (fun p : Fin n → ℝ≥0 =>
    ∑ k, (p k : ℝ≥0∞) • Measure.dirac (x k))
  exact Finset.measurable_sum _ (fun k _ =>
    (measurable_pi_apply k).coe_nnreal_ennreal.smul_measure (Measure.dirac (x k)))

theorem measurable_weightedPointMeasure_of_measurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → X)
    (p : Fin n → Ω → ℝ≥0) (hp : ∀ k, Measurable (p k)) :
    Measurable (fun ω => weightedPointMeasure x (fun k => p k ω)) :=
  (measurable_weightedPointMeasure x).comp (measurable_pi_lambda _ hp)

end Luce
