import Luce.ConvergenceInProbability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Elementary complex estimates for the adapted Bernoulli central limit criterion. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace Luce.BernoulliCLT

def coefficient (u : ℝ) : ℂ := Complex.exp (u * Complex.I) - 1

theorem coefficient_re_nonpos (u : ℝ) : (coefficient u).re ≤ 0 := by
  simp only [coefficient, Complex.sub_re, Complex.one_re]
  rw [Complex.exp_mul_I]
  simp only [Complex.cos_ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.I_im, mul_one, Complex.sin_ofReal_im,
    sub_self, add_zero]
  linarith [Real.cos_le_one u]

theorem coefficient_norm_le {u : ℝ} (hu : |u| ≤ 1) :
    ‖coefficient u‖ ≤ 2 * |u| := by
  simpa [coefficient, norm_mul] using
    Complex.norm_exp_sub_one_le (x := (u : ℂ) * Complex.I) (by simpa using hu)

theorem coefficient_neg_re_le {u : ℝ} (hu : |u| ≤ 1) :
    -(coefficient u).re ≤ u^2 := by
  have h := Complex.norm_exp_sub_one_sub_id_le
    (x := (u : ℂ) * Complex.I) (by simpa using hu)
  have hr := Complex.abs_re_le_norm (Complex.exp ((u : ℂ) * Complex.I) - 1 -
    (u : ℂ) * Complex.I)
  have he : (Complex.exp ((u : ℂ) * Complex.I) - 1 -
      (u : ℂ) * Complex.I).re = (coefficient u).re := by
    simp [coefficient]
  rw [he] at hr
  have hn : ‖(u : ℂ) * Complex.I‖ ^ 2 = u^2 := by simp [sq_abs]
  rw [hn] at h
  exact (neg_le_abs _).trans (hr.trans h)

theorem exp_compensation_error {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp (-z) * (1 + z) - 1‖ ≤ 3 * ‖z‖^2 := by
  have ht := Complex.norm_exp_sub_one_sub_id_le (x := -z) (by simpa using hz)
  simp only [norm_neg] at ht
  have he : Complex.exp (-z) * (1+z) - 1 =
      (Complex.exp (-z) - 1 - -z) * (1+z) - z^2 := by ring
  rw [he]
  calc
    ‖(Complex.exp (-z) - 1 - -z) * (1+z) - z^2‖ ≤
        ‖Complex.exp (-z) - 1 - -z‖ * ‖1+z‖ + ‖z‖^2 := by
      calc
        _ ≤ ‖(Complex.exp (-z) - 1 - -z) * (1+z)‖ + ‖z^2‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul, norm_pow]
    _ ≤ ‖z‖^2 * (1+‖z‖) + ‖z‖^2 := by
      gcongr
      simpa using norm_add_le (1 : ℂ) z
    _ ≤ 3 * ‖z‖^2 := by nlinarith [sq_nonneg ‖z‖]

theorem coefficient_norm_le_two (u : ℝ) : ‖coefficient u‖ ≤ 2 := by
  have h : ‖Complex.exp ((u : ℂ) * Complex.I)‖ = 1 := by simp [Complex.norm_exp]
  exact (norm_sub_le _ _).trans (by norm_num [h])

theorem coefficient_norm_le_all (u : ℝ) : ‖coefficient u‖ ≤ 4 * |u| := by
  by_cases h : |u| ≤ 1
  · exact (coefficient_norm_le h).trans (by nlinarith [abs_nonneg u])
  · have := coefficient_norm_le_two u
    have := lt_of_not_ge h
    linarith

theorem coefficient_neg_re_le_all (u : ℝ) : -(coefficient u).re ≤ 2*u^2 := by
  by_cases h : |u| ≤ 1
  · exact (coefficient_neg_re_le h).trans (by nlinarith [sq_nonneg u])
  · have hr := (neg_le_abs (coefficient u).re).trans
      ((Complex.abs_re_le_norm _).trans (coefficient_norm_le_two u))
    have hu : 1 < |u| := lt_of_not_ge h
    nlinarith [sq_abs u]

theorem norm_exp_le_one {z : ℂ} (hz : z.re ≤ 0) : ‖Complex.exp z‖ ≤ 1 := by
  rw [Complex.norm_exp]
  exact Real.exp_le_one_iff.mpr hz

theorem exp_difference_le {z w : ℂ} (hw : w.re ≤ 0) (hzw : ‖z-w‖ ≤ 1) :
    ‖Complex.exp z - Complex.exp w‖ ≤ 2 * ‖z-w‖ := by
  have he : Complex.exp z - Complex.exp w =
      Complex.exp w * (Complex.exp (z-w) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    simp
  rw [he, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_exp_le_one hw) (norm_nonneg _)).trans
    (by simpa using Complex.norm_exp_sub_one_le hzw)

end Luce.BernoulliCLT
