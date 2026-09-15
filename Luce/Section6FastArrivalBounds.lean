import Luce.Section6PowerIntegrals
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Luce.Section6

theorem one_sub_exp_neg_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1-Real.exp (-x) ∧ 1-Real.exp (-x) ≤ 1 ∧ 1-Real.exp (-x) ≤ x := by
  have he := Real.add_one_le_exp (-x)
  have he1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  exact ⟨sub_nonneg.mpr he1, by linarith [Real.exp_pos (-x)], by linarith⟩

/-- Integrability of the fast-arrival prototype uses alpha>1, exactly as
in the manuscript. It is bounded at zero and has an integrable power tail. -/
theorem integrableOn_fast_arrival {alpha r : ℝ} (ha : 1 < alpha) (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => 1-Real.exp (-(r*s^(-alpha)))) (Ioi 0) := by
  have hnear : IntegrableOn (fun s : ℝ => 1-Real.exp (-(r*s^(-alpha)))) (Ioc 0 1) := by
    apply (integrableOn_const (C := (1 : ℝ)) (s := Ioc (0 : ℝ) 1) (by simp)).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hb := one_sub_exp_neg_bounds (mul_pos hr (Real.rpow_pos_of_pos hs.1 (-alpha))).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2.1
  have hfar : IntegrableOn (fun s : ℝ => 1-Real.exp (-(r*s^(-alpha)))) (Ioi 1) := by
    apply ((integrableOn_Ioi_rpow_of_lt (by linarith : -alpha < -1) zero_lt_one).const_mul r).mono'
      (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hb := one_sub_exp_neg_bounds (mul_pos hr (Real.rpow_pos_of_pos (zero_lt_one.trans hs) (-alpha))).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2.2
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact integrableOn_union.mpr ⟨hnear, hfar⟩

theorem fast_arrival_boundary_continuous {alpha r : ℝ} (hr : 0 < r) :
    ContinuousWithinAt (fun s : ℝ => s*(1-Real.exp (-(r*s^(-alpha))))) (Ici 0) 0 := by
  have hlim : Tendsto (fun s : ℝ => s*(1-Real.exp (-(r*s^(-alpha))))) (𝓝[Ici 0] 0) (𝓝 0) := by
    apply squeeze_zero'
      (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hb := one_sub_exp_neg_bounds (mul_nonneg hr.le (Real.rpow_nonneg hs (-alpha)))
        exact mul_nonneg hs hb.1)
      (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hb := one_sub_exp_neg_bounds (mul_nonneg hr.le (Real.rpow_nonneg hs (-alpha)))
        simpa using mul_le_mul_of_nonneg_left hb.2.1 hs)
      (tendsto_id.mono_left nhdsWithin_le_nhds)
  simpa only [ContinuousWithinAt, zero_mul] using hlim

theorem fast_arrival_boundary_tendsto {alpha r : ℝ} (ha : 1 < alpha) (hr : 0 < r) :
    Tendsto (fun s : ℝ => s*(1-Real.exp (-(r*s^(-alpha))))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun s : ℝ => r*s^(1-alpha)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).const_mul r
    simpa only [neg_sub, mul_zero] using hh
  apply squeeze_zero' _ _ hpow
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    exact mul_nonneg hs.le (one_sub_exp_neg_bounds
      (mul_pos hr (Real.rpow_pos_of_pos hs (-alpha))).le).1
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    have hb := mul_le_mul_of_nonneg_left (one_sub_exp_neg_bounds
      (mul_pos hr (Real.rpow_pos_of_pos hs (-alpha))).le).2.2 hs.le
    have he : s*s^(-alpha) = s^(1-alpha) := by
      conv_lhs => lhs; rw [← Real.rpow_one s]
      rw [← Real.rpow_add hs]
      congr 1
    calc
      _ ≤ s*(r*s^(-alpha)) := hb
      _ = r*(s*s^(-alpha)) := by ring
      _ = _ := by rw [he]

end Luce.Section6
