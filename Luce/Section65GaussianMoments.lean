import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace Luce.Section6

def gaussianMoment65 (v : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ x, x^k ∂gaussianReal 0 v

@[simp] theorem gaussianMoment65_zero (v : ℝ≥0) : gaussianMoment65 v 0 = 1 := by
  simp [gaussianMoment65]

@[simp] theorem gaussianMoment65_one (v : ℝ≥0) : gaussianMoment65 v 1 = 0 := by
  simp [gaussianMoment65]

theorem gaussianMoment65_deriv (v : ℝ≥0) (k : ℕ) :
    gaussianMoment65 v k = iteratedDeriv k (fun t : ℝ => Real.exp (v*t^2/2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v) (by simp) k
  simpa [gaussianMoment65, mgf_id_gaussianReal, Pi.pow_apply] using h.symm

theorem gaussianMoment65_rec (v : ℝ≥0) (k : ℕ) :
    gaussianMoment65 v (k+2) = (v : ℝ)*(k+1)*gaussianMoment65 v k := by
  let f : ℝ → ℝ := fun t => Real.exp (v*t^2/2)
  have hd : deriv f = fun t => (v : ℝ)*(t*f t) := by
    funext t
    dsimp [f]
    rw [_root_.deriv_exp (by fun_prop)]
    simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
      Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul,
      deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
    ring
  rw [gaussianMoment65_deriv, show k+2 = (k+1)+1 from rfl, iteratedDeriv_succ']
  change iteratedDeriv (k+1) (deriv f) 0 = _
  rw [hd, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul (by fun_prop) (by dsimp [f]; fun_prop)]
  simp only [iteratedDeriv_fun_id_zero]
  simp [mul_ite, ite_mul, Nat.choose_one_right, gaussianMoment65_deriv, f, mul_assoc]

end Luce.Section6
