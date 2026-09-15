import Luce.Section6ExtremeScale

noncomputable section
namespace Luce.Section6

/-- Outside the moderate set the numerator depth is larger, and the
exponential argument dominates a positive power of that depth. This single
identity handles the right corner and the reflected left corner. -/
theorem extreme_ratio_bounds {a h b v : ℝ} (ha : 1 ≤ a) (hh : 1 ≤ h)
    (hb : 0 < b) (hv : 0 < v)
    (hext : ¬ (a/h)^b ≤ (min a h)^v) :
    h < a ∧ h < a^(b/(b+v)) ∧ a^(b*v/(b+v)) < (a/h)^b := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hh0 : 0 < h := zero_lt_one.trans_le hh
  have hratio : 0 < a/h := div_pos ha0 hh0
  have hha : h < a := by
    by_contra hn
    have hah : a ≤ h := le_of_not_gt hn
    have hx1 : (a/h)^b ≤ 1 := Real.rpow_le_one hratio.le ((div_le_one hh0).mpr hah) hb.le
    have hm1 : 1 ≤ (min a h)^v := Real.one_le_rpow (le_min ha hh) hv.le
    exact hext (hx1.trans hm1)
  have hex : h^v < (a/h)^b := by simpa only [min_eq_right hha.le] using lt_of_not_ge hext
  have hl := Real.log_lt_log (Real.rpow_pos_of_pos hh0 v) hex
  rw [Real.log_rpow hh0, Real.log_rpow hratio, Real.log_div ha0.ne' hh0.ne'] at hl
  have hsum : 0 < b+v := add_pos hb hv
  have hlog : Real.log h < (b/(b+v))*Real.log a := by
    have he : (b/(b+v))*Real.log a = (b*Real.log a)/(b+v) := by ring
    rw [he]
    apply (lt_div_iff₀ hsum).mpr
    nlinarith
  refine ⟨hha, ?_, ?_⟩
  · apply (Real.log_lt_log_iff hh0 (Real.rpow_pos_of_pos ha0 _)).mp
    rwa [Real.log_rpow ha0]
  · apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos ha0 _) (Real.rpow_pos_of_pos hratio _)).mp
    rw [Real.log_rpow ha0, Real.log_rpow hratio, Real.log_div ha0.ne' hh0.ne']
    have hmul := mul_lt_mul_of_pos_left hlog hb
    have he : b*Real.log a-b*((b/(b+v))*Real.log a) = (b*v/(b+v))*Real.log a := by
      field_simp [hsum.ne']
      ring
    nlinarith

theorem ratio_power_over_depth_le {a h s b : ℝ} (ha : 0 ≤ a) (hh : 1 ≤ h)
    (hs : 1 ≤ s) (hb : 0 ≤ b) : (a/h)^b/s ≤ a^b := by
  have hh0 : 0 < h := zero_lt_one.trans_le hh
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hratio : a/h ≤ a := (div_le_iff₀ hh0).mpr (by nlinarith)
  have hx := Real.rpow_le_rpow (div_nonneg ha hh0.le) hratio hb
  apply (div_le_iff₀ hs0).mpr
  exact hx.trans (by nlinarith [Real.rpow_nonneg ha b])

end Luce.Section6
