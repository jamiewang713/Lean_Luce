import Luce.Section1SukhatmeDefinitions
import Luce.Section6IncrementDensity
import Luce.Section65CoefficientPositivity

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Convolution
namespace Luce.Sukhatme
open Section6

theorem density_eq_incrementDensity : density = incrementDensity 1 1 := by
  funext w
  simp [density, incrementDensity]

theorem convolution_eq (k : ℕ) : convolution k = convolutionDensity 1 1 k := by
  induction k with
  | zero => exact density_eq_incrementDensity
  | succ k ih => simp only [convolution, convolutionDensity, density_eq_incrementDensity, ih]

theorem rightCoefficient_eq (k : ℕ) :
    cornerCoefficient .right (.power 1 1 1) k = coefficient k := by
  norm_num [cornerCoefficient, coefficient, convolution_eq, Real.Gamma_nat_eq_factorial]

theorem totalCoefficient_eq (k : ℕ) :
    totalCoefficient (.finite 1) (.power 1 1 1) k = coefficient k := by
  simpa only [totalCoefficient, cornerCoefficient, zero_add] using rightCoefficient_eq k

theorem coefficient_zero : coefficient 0 = Real.exp (-1) := by
  simp [coefficient, convolution, density]

theorem density_mul_neg (w : ℝ) :
    density w * density (-w) = Real.exp (-Real.exp w - Real.exp (-w)) := by
  simp only [density, ← Real.exp_add]
  congr 1
  ring

theorem coefficient_one_integral :
    coefficient 1 = (1 / 2 : ℝ) * ∫ w : ℝ, Real.exp (-Real.exp w - Real.exp (-w)) := by
  simp only [coefficient, convolution, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul, zero_sub, density_mul_neg]
  norm_num
  ring

theorem bessel_integrand_integrable :
    Integrable (fun w : ℝ => Real.exp (-2 * Real.cosh w)) := by
  have hp := incrementDensity_integrable (gamma := 1) (q := 1) (by norm_num) (by norm_num)
  rw [← density_eq_incrementDensity] at hp
  have hprod : Integrable (fun w => density w * density (-w)) := by
    apply hp.mul_bdd (c := Real.exp (-1))
    · exact (show Continuous (fun w => density (-w)) by
        rw [density_eq_incrementDensity]
        exact (incrementDensity_continuous 1 1).comp continuous_neg).aestronglyMeasurable
    · filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_of_pos (by unfold density; positivity)]
      simpa only [density_eq_incrementDensity, one_mul] using
        incrementDensity_bound (gamma := 1) (q := 1) (by norm_num) (by norm_num) (-w)
  convert hprod using 1
  funext w
  rw [density_mul_neg, Real.cosh_eq]
  congr 1
  ring

theorem coefficient_one : coefficient 1 = besselK0 2 := by
  rw [coefficient_one_integral]
  have he (w : ℝ) : Real.exp (-Real.exp w - Real.exp (-w)) =
      Real.exp (-2 * Real.cosh w) := by rw [Real.cosh_eq]; congr 1; ring
  simp_rw [he]
  have hneg : (∫ w in Iic (0 : ℝ), Real.exp (-2 * Real.cosh w)) =
      ∫ w in Ioi (0 : ℝ), Real.exp (-2 * Real.cosh w) := by
    have h := integral_comp_neg_Ioi 0 (fun w : ℝ => Real.exp (-2 * Real.cosh w))
    simpa only [neg_zero, Real.cosh_neg] using h.symm
  have hsplit := integral_add_compl (s := Iic (0 : ℝ))
    measurableSet_Iic bessel_integrand_integrable
  rw [compl_Iic, hneg] at hsplit
  change (1 / 2 : ℝ) * _ = ∫ w in Ioi (0 : ℝ), Real.exp (-2 * Real.cosh w)
  linarith

end Luce.Sukhatme
