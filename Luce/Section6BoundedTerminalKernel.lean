import Luce.Section6LogarithmicSurvival

noncomputable section
namespace Luce.Section6

/-- Numerical comparison for a fixed terminal window. The concrete theorem
derives the rate lower bound from its finite positive endpoint limit. -/
theorem bounded_terminal_logarithmic_kernel {n H m theta b d : ℝ}
    (hH1 : 1 ≤ H) (hm1 : 1 ≤ m) (hmH : m ≤ H) (hHn : H^2 ≤ n)
    (hb : 0 < b) (hbt : b ≤ theta) (hd : 0 < d) :
    Real.exp (-d*(theta*Real.log (n/H)))+Real.exp (-d*Real.sqrt (n*H)) ≤
      (1+H/b)*((theta/m)*Real.exp (-(d/2)*(theta*Real.log (n/m)))+
        Real.exp (-(d/2)*Real.sqrt (n*m))) := by
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have hHle : H ≤ n := by nlinarith
  have hn : 0 < n := hH.trans_le hHle
  have ht : 0 < theta := hb.trans_le hbt
  have hlog : Real.log (n/m) ≤ 2*Real.log (n/H) := by
    have he := Real.log_le_log (sq_pos_of_pos hH) hHn
    rw [Real.log_pow] at he
    rw [Real.log_div hn.ne' hm.ne', Real.log_div hn.ne' hH.ne']
    have hmLog := Real.log_nonneg hm1
    norm_num only [Nat.cast_ofNat] at he
    linarith
  have he1 : Real.exp (-d*(theta*Real.log (n/H))) ≤
      Real.exp (-(d/2)*(theta*Real.log (n/m))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog (mul_pos hd ht).le]
  have hroot : Real.sqrt (n*m) ≤ Real.sqrt (n*H) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmH hn.le)
  have he2 : Real.exp (-d*Real.sqrt (n*H)) ≤
      Real.exp (-(d/2)*Real.sqrt (n*m)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hroot hd.le, Real.sqrt_nonneg (n*m)]
  have hcoef : 1 ≤ (H/b)*(theta/m) := by
    rw [div_mul_div_comm]
    apply (le_div_iff₀ (mul_pos hb hm)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmH hb.le,
      mul_le_mul_of_nonneg_left hbt hH.le]
  have he3 := mul_le_mul_of_nonneg_right hcoef
    (Real.exp_pos (-(d/2)*(theta*Real.log (n/m)))).le
  have hextra : 0 ≤ (theta/m)*Real.exp (-(d/2)*(theta*Real.log (n/m))) := by positivity
  have hextra2 : 0 ≤ (H/b)*Real.exp (-(d/2)*Real.sqrt (n*m)) := by positivity
  nlinarith

end Luce.Section6
