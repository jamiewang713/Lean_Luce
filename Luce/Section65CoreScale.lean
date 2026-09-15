import Luce.Section65CoreDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Filter
open scoped Topology
namespace Luce.Section6

theorem log_core_lower_sqrt_tendsto65 :
    Tendsto (fun n : ℕ => Real.log (idealCoreLower n : ℝ)/Real.sqrt (Real.log (n : ℝ)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp hlog).const_mul (Real.log 2)
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp hlog
  have hlim := h1.add h2
  simp only [mul_zero, zero_add] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    div_nonneg (Real.log_natCast_nonneg _) (Real.sqrt_nonneg _))) ?_ hlim
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  let l := Real.log (n : ℝ)
  have hl : 0 < l := hn
  have hA : (0 : ℝ) < idealCoreLower n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (idealCoreLower_pos68 n))
  have he : 1 ≤ Real.exp (l^(1/4 : ℝ)) :=
    Real.one_le_exp_iff.mpr (Real.rpow_nonneg hl.le _)
  have hceil : (idealCoreLower n : ℝ) ≤ 2*Real.exp (l^(1/4 : ℝ)) :=
    (Nat.ceil_lt_add_one (Real.exp_pos _).le).le.trans (by linarith)
  have hbound := Real.log_le_log hA hceil
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hbound
  apply (div_le_div_of_nonneg_right hbound (Real.sqrt_nonneg l)).trans_eq
  rw [add_div, Real.sqrt_eq_rpow]
  have hid : l^(1/4 : ℝ)/l^(1/2 : ℝ) = l^(-(1/4 : ℝ)) := by
    rw [← Real.rpow_sub hl]
    norm_num
  change Real.log 2/l^(1/2 : ℝ)+l^(1/4 : ℝ)/l^(1/2 : ℝ) =
    Real.log 2*l^(-(1/2 : ℝ))+l^(-(1/4 : ℝ))
  rw [hid]
  rw [div_eq_mul_inv, ← Real.rpow_neg hl.le]

theorem one_add_log_core_lower_sqrt_tendsto65 :
    Tendsto (fun n : ℕ => (1+Real.log (idealCoreLower n : ℝ))/Real.sqrt (Real.log (n : ℝ)))
      atTop (𝓝 0) := by
  have hs := Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hi := tendsto_inv_atTop_zero.comp hs
  have h := hi.add log_core_lower_sqrt_tendsto65
  simpa only [add_div, one_div, zero_add, Function.comp_apply] using h

end Luce.Section6
