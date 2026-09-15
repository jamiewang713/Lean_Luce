import Luce.Section6ContractDefinitions
import Luce.Section65GaussianMoments
import Luce.Section65LinearMomentExpansion
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal
namespace Luce.Section6

variable {ι : Type*} [Fintype ι]

theorem standardNormalVector_mixed_integrable65 (r : ι → ℕ) :
    Integrable (fun z : ι → ℝ => ∏ i, z i^(r i)) (standardNormalVector ι) := by
  apply Integrable.fintype_prod
  intro i
  exact integrable_pow_of_mem_interior_integrableExpSet
    (X := id) (μ := gaussianReal 0 1) (by simp) (r i)

theorem standardNormalVector_mixed_moment65 (r : ι → ℕ) :
    (∫ z : ι → ℝ, ∏ i, z i^(r i) ∂standardNormalVector ι) =
      ∏ i, gaussianMoment65 1 (r i) := by
  exact integral_fintype_prod_eq_prod (fun i x => x^(r i))

theorem standardNormalVector_linear_exp65 (t : ι → ℝ) (a : ℝ) :
    Integrable (fun z => Real.exp (a*linearCombination65 t z)) (standardNormalVector ι) := by
  have he (z : ι → ℝ) : Real.exp (a*linearCombination65 t z) =
      ∏ i : ι, Real.exp ((a*t i)*z i) := by
    rw [linearCombination65, Finset.mul_sum, Real.exp_sum]
    congr 1
    funext i
    ring
  simp_rw [he]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (a*t i))

theorem standardNormalVector_linear_memLp65 (t : ι → ℝ) (k : ℕ) :
    MemLp (linearCombination65 t) k (standardNormalVector ι) := by
  have he : integrableExpSet (linearCombination65 t) (standardNormalVector ι) = univ := by
    ext a
    simp only [mem_univ, iff_true, integrableExpSet, mem_setOf_eq]
    exact standardNormalVector_linear_exp65 t a
  exact memLp_of_mem_interior_integrableExpSet (by rw [he]; simp) (k : ℝ≥0)

theorem standardNormalVector_linear_expabs65 (t : ι → ℝ) :
    Integrable (fun z => Real.exp (2*|linearCombination65 t z|)) (standardNormalVector ι) :=
  integrable_exp_mul_abs (standardNormalVector_linear_exp65 t 2)
    (standardNormalVector_linear_exp65 t (-2))

theorem standardNormalVector_linear_moment65 [DecidableEq ι] (t : ι → ℝ) (k : ℕ) :
    (∫ z, linearCombination65 t z^k ∂standardNormalVector ι) =
      ∑ v : Fin k → ι, (∏ j : Fin k, t (v j))*∏ i, gaussianMoment65 1 (multiplicity65 v i) := by
  simp_rw [linearCombination65_power]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, standardNormalVector_mixed_moment65]
  · intro v hv
    exact (standardNormalVector_mixed_integrable65 (multiplicity65 v)).const_mul _

end Luce.Section6
