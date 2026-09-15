import Luce.ExponentialFacts
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The mixed exponential moments used by Lemma 5.2

Source: `fixed_points.tex:1025–1048`. These lemmas prove integrability as
well as the factorial moments, before using product-integral identities.
The application to actual race gaps requires the separate exact gap law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Luce

set_option backward.isDefEq.respectTransparency false

private lemma exponential_one_density_pow (p : ℕ) :
    (fun x : ℝ => (exponentialPDF 1 x).toReal * x ^ p) =
      (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x) * x ^ p) := by
  funext x
  rw [exponentialPDF_eq]
  by_cases hx : 0 ≤ x
  · simp [hx, ENNReal.toReal_ofReal, (Real.exp_pos (-x)).le]
  · simp [hx]

/-- Every natural moment is integrable under the rate-one exponential law.
No totalized integral is used to infer integrability. -/
theorem integrable_pow_expMeasure_one (p : ℕ) :
    Integrable (fun x : ℝ => x ^ p) (expMeasure 1) := by
  change Integrable (fun x : ℝ => x ^ p) (volume.withDensity (exponentialPDF 1))
  rw [integrable_withDensity_iff_integrable_smul'
    (show Measurable (exponentialPDF 1) from (measurable_exponentialPDFReal 1).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  rw [exponential_one_density_pow]
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  have hi := Real.GammaIntegral_convergent (show (0 : ℝ) < (p : ℝ) + 1 by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at hi
  exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hi

/-- The exact natural moment, including the zeroth moment. -/
theorem integral_pow_expMeasure_one (p : ℕ) :
    (∫ x : ℝ, x ^ p ∂expMeasure 1) = (p.factorial : ℝ) := by
  change (∫ x : ℝ, x ^ p ∂volume.withDensity (exponentialPDF 1)) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (show AEMeasurable (exponentialPDF 1) volume from
      (measurable_exponentialPDFReal 1).ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  rw [exponential_one_density_pow, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (show (0 : ℝ) < (p : ℝ) + 1 by positivity) (show (0 : ℝ) < 1 by norm_num)
  simpa only [add_sub_cancel_right, Real.rpow_natCast, one_div_one, Real.one_rpow,
    one_mul, mul_one, mul_comm, Real.Gamma_nat_eq_factorial] using hi

/-- Independent unit-exponential coordinates have all mixed moments.
The finite index type can be empty, and powers can be zero. -/
theorem integrable_mixed_expMeasure_one {ι : Type*} [Fintype ι] (p : ι → ℕ) :
    Integrable (fun x : ι → ℝ => ∏ i, x i ^ p i)
      (Measure.pi fun _ : ι => expMeasure 1) := by
  letI := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  exact Integrable.fintype_prod (fun i => integrable_pow_expMeasure_one (p i))

/-- Exact joint mixed moment; distinct gaps are represented by distinct
coordinates of the product law, with no asserted independence of raw gaps. -/
theorem integral_mixed_expMeasure_one {ι : Type*} [Fintype ι] (p : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, x i ^ p i ∂Measure.pi (fun _ : ι => expMeasure 1)) =
      ∏ i, ((p i).factorial : ℝ) := by
  letI := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  rw [integral_fintype_prod_eq_prod (fun i x => x ^ p i)]
  simp only [integral_pow_expMeasure_one]

private lemma coordinate_mul_prod_eq_mixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (x : ι → ℝ) :
    x i * ∏ j, x j = ∏ j, x j ^ (if j = i then 2 else 1) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun j => x j) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => x j ^ (if j = i then 2 else 1))
      (Finset.mem_univ i)]
  simp only [ite_true]
  have he : (∏ j ∈ Finset.univ.erase i, x j ^ (if j = i then 2 else 1)) =
      ∏ j ∈ Finset.univ.erase i, x j := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Finset.ne_of_mem_erase hj]
  rw [he]
  ring

/-- Integrability of the exact multigap Taylor envelope. -/
theorem integrable_sum_mul_prod_expMeasure_one {ι : Type*} [Fintype ι] :
    Integrable (fun x : ι → ℝ => (∑ i, x i) * ∏ i, x i)
      (Measure.pi fun _ : ι => expMeasure 1) := by
  classical
  simp_rw [Finset.sum_mul, coordinate_mul_prod_eq_mixed]
  exact integrable_finset_sum Finset.univ (fun i _ => integrable_mixed_expMeasure_one _)

/-- The Taylor envelope has expectation twice the number of selected gaps.
This explicitly accounts for the squared coordinate in every summand. -/
theorem integral_sum_mul_prod_expMeasure_one {ι : Type*} [Fintype ι] :
    (∫ x : ι → ℝ, (∑ i, x i) * ∏ i, x i ∂Measure.pi (fun _ : ι => expMeasure 1)) =
      2 * (Fintype.card ι : ℝ) := by
  classical
  simp_rw [Finset.sum_mul, coordinate_mul_prod_eq_mixed]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_mixed_expMeasure_one _)]
  have he (i : ι) : (∏ j : ι, ((if j = i then 2 else 1 : ℕ).factorial : ℝ)) = 2 := by
    rw [Finset.prod_eq_single i]
    · norm_num
    · intro j _ hji
      simp [hji]
    · simp
  simp_rw [integral_mixed_expMeasure_one, he]
  simp [mul_comm]

end Luce
