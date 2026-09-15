import Luce.Section6Sampling

noncomputable section
namespace Luce.Section6

/-- Unit-cell depth comparison for arbitrary real powers, including the
negative exponents in the active-right kernel. -/
theorem comparable_depth_rpow_bounds {h x : ℝ} (hh : 0 < h)
    (hhx : h ≤ x) (hxh : x ≤ 2*h) (s : ℝ) :
    h^s ≤ (2 : ℝ)^|s| * x^s ∧ x^s ≤ (2 : ℝ)^|s| * h^s := by
  have hx : 0 < x := hh.trans_le hhx
  have htwo : (1 : ℝ) ≤ (2 : ℝ)^|s| := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs] at *
    constructor
    · exact (Real.rpow_le_rpow hh.le hhx hs).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg hx.le _) htwo)
    · have he := Real.rpow_le_rpow hx.le hxh hs
      simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hh.le] using he
  · have hs0 : s ≤ 0 := le_of_not_ge hs
    constructor
    · have he : h^s ≤ (x/2)^s := Real.rpow_le_rpow_of_nonpos
        (div_pos hx (by norm_num)) (by linarith) hs0
      have hid : (x/2)^s = (2 : ℝ)^|s| * x^s := by
        rw [Real.div_rpow hx.le (by norm_num), abs_of_nonpos hs0, Real.rpow_neg (by norm_num)]
        ring
      exact he.trans_eq hid
    · exact (Real.rpow_le_rpow_of_nonpos hh hhx hs0).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg hh.le _) htwo)

end Luce.Section6
