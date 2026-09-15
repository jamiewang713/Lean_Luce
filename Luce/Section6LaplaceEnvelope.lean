import Luce.Section6TraceDensity

noncomputable section
open MeasureTheory Set
namespace Luce.Section6

theorem integral_exp_neg_abs68 {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, Real.exp (-c*|x|)) = 2/c := by
  have hl : (∫ x in Iic (0 : ℝ), Real.exp (-c*|x|)) = 1/c := by
    have he : (∫ x in Iic (0 : ℝ), Real.exp (-c*|x|)) =
        ∫ x in Iic (0 : ℝ), Real.exp (c*x) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x hx
      change Real.exp (-c*|x|) = Real.exp (c*x)
      rw [abs_of_nonpos (show x ≤ 0 from hx)]
      congr 1
      ring
    rw [he, integral_exp_mul_Iic hc]
    simp
  have hr : (∫ x in Ioi (0 : ℝ), Real.exp (-c*|x|)) = 1/c := by
    have he : (∫ x in Ioi (0 : ℝ), Real.exp (-c*|x|)) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-c*x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change Real.exp (-c*|x|) = Real.exp (-c*x)
      rw [abs_of_pos (show 0 < x from hx)]
    rw [he, integral_exp_mul_Ioi (neg_neg_of_pos hc)]
    simp
  have he := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic (integrable_exp_neg_abs68 hc)
  rw [compl_Iic, hl, hr] at he
  rw [← he]
  ring

def laplaceDensity68 (c x : ℝ) : ℝ := (c/2)*Real.exp (-c*|x|)

theorem laplaceDensity68_traceDensity {c : ℝ} (hc : 0 < c) :
    TraceDensity68 (laplaceDensity68 c) where
  nonneg x := by unfold laplaceDensity68; positivity
  continuous := by unfold laplaceDensity68; fun_prop
  integrable := (integrable_exp_neg_abs68 hc).const_mul (c/2)
  integral_one := by
    unfold laplaceDensity68
    rw [integral_const_mul, integral_exp_neg_abs68 hc]
    field_simp
  bounded := ⟨c/2, by positivity, fun x => by
    unfold laplaceDensity68
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (abs_nonneg x)))⟩

end Luce.Section6
