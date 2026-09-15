import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open MeasureTheory Complex Set
open scoped BigOperators
namespace Luce.Section6

def momentTaylor (μ : Measure ℝ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n+1), (j.factorial : ℂ)⁻¹ * I^j * (∫ x, x^j ∂μ)

theorem charFun_derivative_moment_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (h : MemLp id n μ) (t : ℝ) :
    ‖iteratedDeriv n (charFun μ) t‖ ≤ ∫ x, |x|^n ∂μ := by
  rw [iteratedDeriv_charFun h, norm_mul, norm_pow, norm_I, one_pow, one_mul]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with x
  simp [norm_mul, norm_pow, Complex.norm_exp, Complex.mul_re, Complex.exp_re,
    Real.norm_eq_abs]

theorem momentTaylor_eq_taylor (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (h : ∀ j : ℕ, MemLp id j μ) :
    momentTaylor μ n = taylorWithinEval (charFun μ) n (Icc 0 1) 0 1 := by
  have hdiff : ∀ j : ℕ, ContDiff ℝ j (charFun μ) := fun j => contDiff_charFun (h j)
  rw [taylor_within_apply]
  unfold momentTaylor
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    (hdiff j).contDiffAt (by constructor <;> norm_num), iteratedDeriv_charFun_zero (h j)]
  simp [RCLike.real_smul_eq_coe_mul, mul_assoc]

/-- A global finite Taylor bound; it requires only finite moments.
The denominator n! is sufficient for the later Gaussian remainder limit. -/
theorem charFun_momentTaylor_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : ∀ j : ℕ, MemLp id j μ) (n : ℕ) :
    ‖charFun μ 1 - momentTaylor μ n‖ ≤ (∫ x, |x|^(n+1) ∂μ)/(n.factorial : ℝ) := by
  rw [momentTaylor_eq_taylor μ n h]
  have hd : ContDiff ℝ (n+1) (charFun μ) := contDiff_charFun (h (n+1))
  have hh := taylor_mean_remainder_bound (f := charFun μ) (a := 0) (b := 1) (x := 1)
    (by norm_num) hd.contDiffOn (by constructor <;> norm_num)
    (C := ∫ x, |x|^(n+1) ∂μ) (fun y hy => ?_)
  · simpa using hh
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    hd.contDiffAt hy]
  exact charFun_derivative_moment_bound μ (n+1) (h (n+1)) y

end Luce.Section6
