import Luce.Section6UniformMomentDecay

noncomputable section
namespace Luce.Section6

theorem exp_neg_min_le_sum (d x y : ℝ) :
    Real.exp (-d*min x y) ≤ Real.exp (-d*x)+Real.exp (-d*y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    linarith [Real.exp_pos (-d*y)]
  · rw [min_eq_right h]
    linarith [Real.exp_pos (-d*x)]

theorem sum_exp_neg_le_twice_min {d x y : ℝ} (hd : 0 ≤ d) :
    Real.exp (-d*x)+Real.exp (-d*y) ≤ 2*Real.exp (-d*min x y) := by
  have hx : Real.exp (-d*x) ≤ Real.exp (-d*min x y) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (min_le_left x y) hd])
  have hy : Real.exp (-d*y) ≤ Real.exp (-d*min x y) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (min_le_right x y) hd])
  linarith

end Luce.Section6
