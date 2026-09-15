import Luce.Section2FinitePointMeasure
import Luce.Section2PoissonMixture
import Mathlib.MeasureTheory.Integral.Pi

/-! # The finite-intensity Poisson iid construction

The law is a Poisson mixture of actual finite sums of Dirac measures. The
zero-intensity case does not require a point in the underlying space. This
module proves the probability and Laplace identities of this construction;
the disjoint-count characterization is a separate result.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators

namespace Luce

variable {X : Type*} [MeasurableSpace X]

theorem integral_pointMeasureOfFin {m : ℕ} (x : Fin m → X)
    (g : X → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂(pointMeasureOfFin x : Measure X)) = ∑ i, g (x i) := by
  simp only [pointMeasureOfFin, FiniteMeasure.toMeasure_sum]
  change (∫ y, g y ∂(∑ i, Measure.dirac (x i))) = ∑ i, g (x i)
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac' hg.stronglyMeasurable (by simp))]
  simp only [integral_dirac' _ _ hg.stronglyMeasurable]

theorem integrable_pointMeasure (μ : FinitePointMeasure X)
    (g : X → ℝ) (hg : Measurable g) :
    Integrable g (μ.toFiniteMeasure : Measure X) := by
  obtain ⟨m, x, hx⟩ := μ.property
  change Integrable g (μ.val : Measure X)
  rw [← hx]
  simp only [pointMeasureOfFin, FiniteMeasure.toMeasure_sum]
  change Integrable g (∑ i, Measure.dirac (x i))
  exact integrable_finsetSum_measure.mpr fun i _ =>
    integrable_dirac' hg.stronglyMeasurable (by simp)

/-- The ordinary Laplace test on an actual finite point measure. -/
noncomputable def pointLaplace (g : X → ℝ) (μ : FinitePointMeasure X) : ℝ :=
  Real.exp (-(∫ x, g x ∂(μ.toFiniteMeasure : Measure X)))

theorem measurable_pointLaplace (g : X → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) : Measurable (pointLaplace g) := by
  have heq : (fun μ : FinitePointMeasure X => ∫ x, g x ∂(μ.toFiniteMeasure : Measure X)) =
      fun μ => (∫⁻ x, ENNReal.ofReal (g x) ∂(μ.toFiniteMeasure : Measure X)).toReal := by
    funext μ
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0)
      hg.aestronglyMeasurable
  unfold pointLaplace
  change Measurable ((fun t : ℝ => Real.exp (-t)) ∘
    (fun μ : FinitePointMeasure X => ∫ x, g x ∂(μ.toFiniteMeasure : Measure X)))
  rw [heq]
  exact (measurable_id.neg.exp).comp
    ((Measure.measurable_lintegral hg.ennreal_ofReal).comp
      FinitePointMeasure.measurable_toMeasure).ennreal_toReal

theorem pointLaplace_mem_Icc (g : X → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (μ : FinitePointMeasure X) : 0 ≤ pointLaplace g μ ∧ pointLaplace g μ ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (integral_nonneg hg0))

@[simp] theorem pointLaplace_zero (g : X → ℝ) :
    pointLaplace g (0 : FinitePointMeasure X) = 1 := by
  simp [pointLaplace]

theorem pointLaplace_ofFin {m : ℕ} (x : Fin m → X)
    (g : X → ℝ) (hg : Measurable g) :
    pointLaplace g (FinitePointMeasure.ofFin x) = ∏ i, Real.exp (-g (x i)) := by
  rw [pointLaplace, FinitePointMeasure.toFiniteMeasure_ofFin,
    integral_pointMeasureOfFin x g hg, ← Finset.sum_neg_distrib, Real.exp_sum]

/-- The point measure of `m` independent samples with common probability law `p`. -/
noncomputable def iidPointLaw (p : ProbabilityMeasure X) (m : ℕ) :
    Measure (FinitePointMeasure X) :=
  (Measure.pi fun _ : Fin m => (p : Measure X)).map FinitePointMeasure.ofFin

instance iidPointLaw_isProbabilityMeasure (p : ProbabilityMeasure X) (m : ℕ) :
    IsProbabilityMeasure (iidPointLaw p m) :=
  Measure.isProbabilityMeasure_map FinitePointMeasure.measurable_ofFin.aemeasurable

theorem integral_pointLaplace_iidPointLaw (p : ProbabilityMeasure X) (m : ℕ)
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ μ, pointLaplace g μ ∂iidPointLaw p m) =
      (∫ x, Real.exp (-g x) ∂(p : Measure X)) ^ m := by
  rw [iidPointLaw, integral_map FinitePointMeasure.measurable_ofFin.aemeasurable
    (measurable_pointLaplace g hg hg0).aestronglyMeasurable]
  simp_rw [pointLaplace_ofFin _ g hg]
  simpa only [Fintype.card_fin] using
    (integral_fintype_prod_eq_pow (ι := Fin m) (μ := (p : Measure X))
      (fun x => Real.exp (-g x)))

private theorem nonempty_of_finiteMeasure_ne_zero (ν : FiniteMeasure X) (hν : ν ≠ 0) :
    Nonempty X := by
  have hmass : (ν : Measure X) Set.univ ≠ 0 := by
    rw [← FiniteMeasure.ennreal_mass]
    exact ENNReal.coe_ne_zero.mpr (ν.mass_nonzero_iff.mpr hν)
  exact ⟨(nonempty_of_measure_ne_zero hmass).choose⟩

/-- A finite-intensity Poisson law, constructed by a Poisson count and iid
locations. The zero law is defined even when the underlying space is empty. -/
noncomputable def finitePoissonLaw (ν : FiniteMeasure X) :
    Measure (FinitePointMeasure X) := by
  classical
  exact if hν : ν = 0 then Measure.dirac 0 else
    letI := nonempty_of_finiteMeasure_ne_zero ν hν
    poissonMixture ν.mass (iidPointLaw ν.normalize)

@[simp] theorem finitePoissonLaw_zero :
    finitePoissonLaw (0 : FiniteMeasure X) = Measure.dirac 0 := by
  simp [finitePoissonLaw]

theorem finitePoissonLaw_of_ne_zero [Nonempty X] (ν : FiniteMeasure X) (hν : ν ≠ 0) :
    finitePoissonLaw ν = poissonMixture ν.mass (iidPointLaw ν.normalize) := by
  simp [finitePoissonLaw, hν]

instance finitePoissonLaw_isProbabilityMeasure (ν : FiniteMeasure X) :
    IsProbabilityMeasure (finitePoissonLaw ν) := by
  classical
  by_cases hν : ν = 0
  · subst ν
    rw [finitePoissonLaw_zero]
    infer_instance
  · let := nonempty_of_finiteMeasure_ne_zero ν hν
    rw [finitePoissonLaw_of_ne_zero ν hν]
    infer_instance

theorem integrable_exp_neg (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    Integrable (fun x => Real.exp (-g x)) μ := by
  apply (integrable_const (1 : ℝ)).mono' hg.neg.exp.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg0 x))

theorem integrable_one_sub_exp_neg (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    Integrable (fun x => 1 - Real.exp (-g x)) μ :=
  (integrable_const 1).sub (integrable_exp_neg μ g hg hg0)

theorem integral_exp_neg_mem_Icc (p : ProbabilityMeasure X)
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    0 ≤ (∫ x, Real.exp (-g x) ∂(p : Measure X)) ∧
      (∫ x, Real.exp (-g x) ∂(p : Measure X)) ≤ 1 := by
  refine ⟨integral_nonneg (fun x => (Real.exp_pos _).le), ?_⟩
  calc
    _ ≤ ∫ _ : X, (1 : ℝ) ∂(p : Measure X) :=
      integral_mono (integrable_exp_neg (p : Measure X) g hg hg0)
        (integrable_const 1) (fun x => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg0 x)))
    _ = 1 := by simp

theorem integral_one_sub_exp_neg_eq_mass_mul [Nonempty X]
    (ν : FiniteMeasure X) (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x, (1 - Real.exp (-g x)) ∂(ν : Measure X)) =
      (ν.mass : ℝ) * (1 - ∫ x, Real.exp (-g x) ∂(ν.normalize : Measure X)) := by
  have hν : (ν : Measure X) = ν.mass • (ν.normalize : Measure X) := by
    exact congrArg (fun μ : FiniteMeasure X => (μ : Measure X))
      ν.self_eq_mass_smul_normalize
  calc
    _ = (ν.mass : ℝ) *
        (∫ x, (1 - Real.exp (-g x)) ∂(ν.normalize : Measure X)) := by
      nth_rw 1 [hν]
      rw [integral_smul_nnreal_measure]
      rfl
    _ = _ := by
      rw [integral_sub (integrable_const 1)
        (integrable_exp_neg (ν.normalize : Measure X) g hg hg0)]
      simp

theorem integrable_pointLaplace_finitePoissonLaw (ν : FiniteMeasure X)
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    Integrable (pointLaplace g) (finitePoissonLaw ν) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_pointLaplace g hg hg0).aestronglyMeasurable
  exact Eventually.of_forall fun μ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pointLaplace_mem_Icc g hg0 μ).1]
    exact (pointLaplace_mem_Icc g hg0 μ).2

/-- The Laplace functional of the finite-intensity Poisson iid construction.
The intensity may vanish and the spatial measurable space may be empty.
Every measurable nonnegative real test is allowed; its intensity integral
need not be finite. The integrand on the right is automatically bounded. -/
theorem integral_pointLaplace_finitePoissonLaw (ν : FiniteMeasure X)
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ μ, pointLaplace g μ ∂finitePoissonLaw ν) =
      Real.exp (-(∫ x, (1 - Real.exp (-g x)) ∂(ν : Measure X))) := by
  classical
  by_cases hν : ν = 0
  · subst ν
    rw [finitePoissonLaw_zero,
      integral_dirac' _ _ (measurable_pointLaplace g hg hg0).stronglyMeasurable]
    simp
  · let := nonempty_of_finiteMeasure_ne_zero ν hν
    rw [finitePoissonLaw_of_ne_zero ν hν]
    have ha := integral_exp_neg_mem_Icc ν.normalize g hg hg0
    rw [integral_poissonMixture_of_power ν.mass (iidPointLaw ν.normalize)
      (pointLaplace g) (measurable_pointLaplace g hg hg0) (pointLaplace_mem_Icc g hg0)
      ha.1 ha.2 (fun m => integral_pointLaplace_iidPointLaw ν.normalize m g hg hg0)]
    rw [integral_one_sub_exp_neg_eq_mass_mul ν g hg hg0]
    congr 1
    ring

end Luce
