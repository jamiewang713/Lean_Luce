import Luce.Section6ContractDefinitions
import Luce.Section6EnvelopeAbsorption
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Luce.Section6

theorem incrementDensity_pos {gamma q : ℝ} (hg : 0 < gamma) (hq : 0 < q) (x : ℝ) :
    0 < incrementDensity gamma q x := by unfold incrementDensity; positivity

theorem incrementDensity_continuous (gamma q : ℝ) : Continuous (incrementDensity gamma q) := by
  unfold incrementDensity
  fun_prop

theorem incrementDensity_hasDerivAt (gamma q x : ℝ) :
    HasDerivAt (incrementDensity gamma q)
      (gamma*incrementDensity gamma q x*(1-q*Real.exp (gamma*x))) x := by
  have he := ((hasDerivAt_id x).const_mul gamma).exp
  have hf := (he.const_mul (-q)).exp
  convert (he.const_mul (gamma*q)).mul hf using 1 <;>
    first | rfl | (simp only [incrementDensity, id_eq, mul_one, neg_mul]; ring)

/-- The exponential change of variables over the entire real line. -/
theorem integral_exp_substitution68 (g : ℝ → ℝ) :
    (∫ x : ℝ, Real.exp x * g (Real.exp x)) = ∫ y in Ioi (0 : ℝ), g y := by
  have hsub := integral_image_eq_integral_abs_deriv_smul
    (show MeasurableSet (univ : Set ℝ) from MeasurableSet.univ)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h) g
  simpa only [image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _), smul_eq_mul,
    Measure.restrict_univ] using hsub.symm

theorem incrementDensity_integral {gamma q : ℝ} (hg : 0 < gamma) (hq : 0 < q) :
    (∫ x : ℝ, incrementDensity gamma q x) = 1 := by
  have hexp : (∫ y in Ioi (0 : ℝ), q*Real.exp (-(q*y))) = 1 := by
    rw [integral_const_mul]
    have hh := integral_exp_mul_Ioi (a := -q) (by linarith) 0
    simp only [mul_zero, Real.exp_zero] at hh
    simp only [neg_mul] at hh
    rw [hh]
    field_simp
  have hchange := integral_exp_substitution68 (fun y => q*Real.exp (-(q*y)))
  rw [hexp] at hchange
  have he (x : ℝ) : incrementDensity gamma q x =
      gamma*(Real.exp (gamma*x)*(q*Real.exp (-(q*Real.exp (gamma*x))))) := by
    unfold incrementDensity
    simp only [neg_mul]
    ring
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun x : ℝ => Real.exp x*(q*Real.exp (-(q*Real.exp x)))) gamma]
  rw [hchange]
  simp [abs_of_pos hg, hg.ne', smul_eq_mul]

theorem incrementDensity_integrable {gamma q : ℝ} (hg : 0 < gamma) (hq : 0 < q) :
    Integrable (incrementDensity gamma q) :=
  Integrable.of_integral_ne_zero (by rw [incrementDensity_integral hg hq]; norm_num)

theorem incrementDensity_bound {gamma q : ℝ} (hg : 0 < gamma) (hq : 0 < q) (x : ℝ) :
    incrementDensity gamma q x ≤ gamma*Real.exp (-1) := by
  have hh := mul_le_mul_of_nonneg_left
    (Real.mul_exp_neg_le_exp_neg_one (q*Real.exp (gamma*x))) hg.le
  convert hh using 1 <;> first | rfl | (simp only [incrementDensity, neg_mul]; ring)

/-- A two-sided exponential envelope is integrable on the full line. -/
theorem integrable_exp_neg_abs68 {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c*|x|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic hc 0).congr_fun _ measurableSet_Iic
    intro x hx
    change Real.exp (c*x) = Real.exp (-c*|x|)
    rw [abs_of_nonpos (show x ≤ 0 from hx)]
    congr 1
    ring
  · apply (integrableOn_exp_mul_Ioi (show -c < 0 by linarith) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    change Real.exp (-c*x) = Real.exp (-c*|x|)
    rw [abs_of_pos (show 0 < x from hx)]

end Luce.Section6
