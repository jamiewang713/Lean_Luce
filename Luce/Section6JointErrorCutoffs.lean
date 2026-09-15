import Luce.Section6Sampling

noncomputable section
namespace Luce.Section6

/-- Choose cutoffs in exactly the manuscript's joint regime. There is
no prescribed convergence rate tying the two parameters together. -/
theorem joint_power_error_small {a C eps : ℝ}
    (ha : 0 < a) (hC : 0 < C) (heps : 0 < eps) :
    ∃ delta M : ℝ, 0 < delta ∧ 0 < M ∧
    ∀ x m : ℝ, 0 < x → x < delta → M ≤ m →
      C*(x^a+1/m) ≤ eps := by
  let delta := (eps/(2*C))^(1/a)
  let M := 2*C/eps
  have hb : 0 < eps/(2*C) := by positivity
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨delta, M, Real.rpow_pos_of_pos hb _, hM, ?_⟩
  intro x m hx hxd hm
  have hm0 : 0 < m := hM.trans_le hm
  have hpow := Real.rpow_le_rpow hx.le hxd.le ha.le
  have hd : delta^a = eps/(2*C) := by
    dsimp [delta]
    rw [← Real.rpow_mul hb.le, show (1/a)*a = (1 : ℝ) by field_simp, Real.rpow_one]
  rw [hd] at hpow
  have hfirst := mul_le_mul_of_nonneg_left hpow hC.le
  have hid : C*(eps/(2*C)) = eps/2 := by field_simp
  rw [hid] at hfirst
  have hsecond : C/m ≤ eps/2 := by
    apply (div_le_iff₀ hm0).mpr
    have hh := mul_le_mul_of_nonneg_left hm (half_pos heps).le
    have hid' : (eps/2)*M = C := by dsimp [M]; field_simp
    rw [hid'] at hh
    exact hh
  calc
    _ = C*x^a+C/m := by ring
    _ ≤ eps/2+eps/2 := add_le_add hfirst hsecond
    _ = _ := by ring

/-- Division of two relative approximations is stable once the
denominator error is proved at most one half. -/
theorem relative_quotient_error {u v e a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hu : |u-1| ≤ a*e) (hv : |v-1| ≤ b*e) (hsmall : b*e ≤ 1/2) :
    |u/v-1| ≤ (2*(a+b))*e := by
  have hvlo : (1/2 : ℝ) ≤ v := by
    have hh := (abs_le.mp hv).1
    linarith
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hvlo
  have hdiff : |u-v| ≤ (a+b)*e := by
    calc
      _ ≤ |u-1|+|1-v| := abs_sub_le u 1 v
      _ = |u-1|+|v-1| := by rw [abs_sub_comm 1 v]
      _ ≤ a*e+b*e := add_le_add hu hv
      _ = _ := by ring
  rw [div_sub_one hv0.ne', abs_div, abs_of_pos hv0]
  apply (div_le_iff₀ hv0).mpr
  have hh := mul_le_mul_of_nonneg_left hvlo (by positivity : 0 ≤ 2*(a+b)*e)
  exact hdiff.trans (by nlinarith)

end Luce.Section6
