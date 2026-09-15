import Luce.Section6FastArrivalPrototype
import Luce.Section6FastWeightedPrototype

noncomputable section
open Set MeasureTheory
namespace Luce.Section6

theorem critical_arrival_linear_error {x : ℝ} (hx : 0 ≤ x) :
    |(1-Real.exp (-x))-x| ≤ x^2 := by
  have hb := one_sub_exp_neg_bounds hx
  have hm : (x+1)*Real.exp (-x) ≤ 1 := by
    calc
      _ ≤ Real.exp x*Real.exp (-x) :=
        mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  rw [abs_of_nonpos (by linarith [hb.2.2])]
  nlinarith [mul_le_mul_of_nonneg_left hb.2.2 hx]

theorem critical_inv_sq_integral {t : ℝ} (ht : 0 < t) :
    (∫ s in t..1, 1/s^2) = 1/t-1 := by
  have h := integral_zpow (a := t) (b := 1) (n := -2)
    (Or.inr ⟨by norm_num,notMem_uIcc_of_lt ht zero_lt_one⟩)
  norm_num only [show (-2 : ℤ)+1 = -1 by norm_num,zpow_neg,zpow_ofNat,one_div,
    zpow_one,one_pow,Nat.cast_ofNat,Int.cast_neg,Int.cast_ofNat,div_neg,div_one] at h
  simpa only [neg_sub,one_div,pow_one] using h

theorem critical_pole_weight_intervalIntegrable {c t b : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s : ℝ => rateKernel t (c/s)) volume 0 b := by
  apply (intervalIntegrable_const (c := Real.exp (-1)/t)).mono_fun' (by
    unfold rateKernel survivalKernel
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le hb] at hs
  rw [Real.norm_eq_abs,abs_of_nonneg (rateKernel_nonneg (div_nonneg hc hs.1.le))]
  exact rateKernel_le_exp_neg_one_div ht

theorem critical_pole_arrival_intervalIntegrable {c t b : ℝ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s : ℝ => 1-survivalKernel t (c/s)) volume 0 b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' (by
    unfold survivalKernel
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le hb] at hs
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr
    (survivalKernel_le_one ht (div_nonneg hc hs.1.le)))]
  exact sub_le_self _ (survivalKernel_pos _ _).le

/-- The weighted pole integral is logarithmic, with a bounded error.
Splitting at t uses only the global kernel maximum and a first-order
exponential estimate. -/
theorem critical_pole_weight_integral {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    |(∫ s in (0 : ℝ)..1, rateKernel t (c/s))-c*Real.log (1/t)| ≤
      Real.exp (-1)+c^2 := by
  have hi := critical_pole_weight_intervalIntegrable hc.le ht zero_le_one
  have hnear : |∫ s in (0 : ℝ)..t, rateKernel t (c/s)| ≤ Real.exp (-1) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (C := Real.exp (-1)/t) (f := fun s => rateKernel t (c/s)) (fun s hs => by
        rw [uIoc_of_le ht.le] at hs
        rw [Real.norm_eq_abs,abs_of_nonneg (rateKernel_nonneg (div_nonneg hc.le hs.1.le))]
        exact rateKernel_le_exp_neg_one_div ht)
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_pos ht,div_mul_cancel₀ _ ht.ne'] using h
  have hinv : IntervalIntegrable (fun s : ℝ => 1/s) volume t 1 :=
    (continuousOn_const.div continuousOn_id (fun s hs => ne_of_gt (ht.trans_le hs.1))).intervalIntegrable_of_Icc ht1
  have hinv2 : IntervalIntegrable (fun s : ℝ => 1/s^2) volume t 1 :=
    (continuousOn_const.div (continuousOn_id.pow 2) (fun s hs => pow_ne_zero _
      (ne_of_gt (ht.trans_le hs.1)))).intervalIntegrable_of_Icc ht1
  have hfar : |∫ s in t..1, rateKernel t (c/s)-c/s| ≤ c^2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le ht1
      (f := fun s => rateKernel t (c/s)-c/s) (g := fun s => (c^2*t)*(1/s^2))
      (ae_of_all _ fun s hs => by
        have hs0 : 0 < s := ht.trans hs.1
        have hcs : 0 ≤ c/s := div_nonneg hc.le hs0.le
        rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (rateKernel_le ht.le hcs))]
        have h := mul_le_mul_of_nonneg_left
          (one_sub_exp_neg_bounds (mul_nonneg ht.le hcs)).2.2 hcs
        change (c/s)*(1-Real.exp (-(t*(c/s)))) ≤ (c/s)*(t*(c/s)) at h
        dsimp [rateKernel,survivalKernel]
        rw [neg_mul]
        convert h using 1 <;> ring)
      (hinv2.const_mul (c^2*t))
    rw [intervalIntegral.integral_const_mul,critical_inv_sq_integral ht,Real.norm_eq_abs] at h
    apply h.trans
    have heq : (c^2*t)*(1/t-1) = c^2*(1-t) := by field_simp
    rw [heq]
    nlinarith [sq_nonneg c]
  have hsplit : (∫ s in (0 : ℝ)..1, rateKernel t (c/s))-c*Real.log (1/t) =
      (∫ s in (0 : ℝ)..t, rateKernel t (c/s))+
        ∫ s in t..1, rateKernel t (c/s)-c/s := by
    have hib : IntervalIntegrable (fun s : ℝ => c/s) volume t 1 := by
      simpa only [mul_one_div] using hinv.const_mul c
    rw [intervalIntegral.integral_sub (hi.mono_set (by
        rw [uIcc_of_le ht1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc ht.le le_rfl)) hib]
    have heq : (∫ s in t..1, c/s) = c*Real.log (1/t) := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul,integral_inv_of_pos ht zero_lt_one]
      simp only [div_eq_mul_inv]
    rw [heq,← intervalIntegral.integral_add_adjacent_intervals
      (critical_pole_weight_intervalIntegrable hc.le ht ht.le)
      (hi.mono_set (by rw [uIcc_of_le ht1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc ht.le le_rfl))]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hnear hfar)

/-- The arrival integral has error O(t), with the logarithmic term
obtained by integrating c*t/s only over [t,1]. -/
theorem critical_pole_arrival_integral {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    |(∫ s in (0 : ℝ)..1, 1-survivalKernel t (c/s))-(c*t)*Real.log (1/t)| ≤
      (1+c^2)*t := by
  have hi := critical_pole_arrival_intervalIntegrable hc.le ht.le zero_le_one
  have hmid := hi.mono_set (show uIcc t 1 ⊆ uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le ht1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc ht.le le_rfl)
  have hnear : |∫ s in (0 : ℝ)..t, 1-survivalKernel t (c/s)| ≤ t := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (C := 1) (f := fun s => 1-survivalKernel t (c/s)) (fun s hs => by
        rw [uIoc_of_le ht.le] at hs
        rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr
          (survivalKernel_le_one ht.le (div_nonneg hc.le hs.1.le)))]
        exact sub_le_self _ (survivalKernel_pos _ _).le)
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_pos ht,one_mul] using h
  have hinv : IntervalIntegrable (fun s : ℝ => 1/s) volume t 1 :=
    (continuousOn_const.div continuousOn_id (fun s hs => ne_of_gt (ht.trans_le hs.1))).intervalIntegrable_of_Icc ht1
  have hinv2 : IntervalIntegrable (fun s : ℝ => 1/s^2) volume t 1 :=
    (continuousOn_const.div (continuousOn_id.pow 2) (fun s hs => pow_ne_zero _
      (ne_of_gt (ht.trans_le hs.1)))).intervalIntegrable_of_Icc ht1
  have hfar : |∫ s in t..1, (1-survivalKernel t (c/s))-(c*t)/s| ≤ c^2*t := by
    have h := intervalIntegral.norm_integral_le_of_norm_le ht1
      (f := fun s => (1-survivalKernel t (c/s))-(c*t)/s)
      (g := fun s => (c*t)^2*(1/s^2))
      (ae_of_all _ fun s hs => by
        have hs0 : 0 < s := ht.trans hs.1
        have h := critical_arrival_linear_error (x := (c*t)/s) (by positivity)
        rw [Real.norm_eq_abs]
        convert h using 1 <;> first | rfl | (simp only [survivalKernel,neg_mul]; congr 2 <;> ring) | ring)
      (hinv2.const_mul ((c*t)^2))
    rw [intervalIntegral.integral_const_mul,critical_inv_sq_integral ht,Real.norm_eq_abs] at h
    apply h.trans
    have heq : (c*t)^2*(1/t-1) = (c^2*t)*(1-t) := by field_simp
    rw [heq]
    nlinarith [mul_nonneg (sq_nonneg c) ht.le]
  have hsplit : (∫ s in (0 : ℝ)..1, 1-survivalKernel t (c/s))-(c*t)*Real.log (1/t) =
      (∫ s in (0 : ℝ)..t, 1-survivalKernel t (c/s))+
        ∫ s in t..1, (1-survivalKernel t (c/s))-(c*t)/s := by
    have hib : IntervalIntegrable (fun s : ℝ => (c*t)/s) volume t 1 := by
      simpa only [mul_one_div] using hinv.const_mul (c*t)
    rw [intervalIntegral.integral_sub hmid hib]
    have heq : (∫ s in t..1, (c*t)/s) = (c*t)*Real.log (1/t) := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul,integral_inv_of_pos ht zero_lt_one]
      simp only [div_eq_mul_inv]
    rw [heq,← intervalIntegral.integral_add_adjacent_intervals
      (critical_pole_arrival_intervalIntegrable hc.le ht.le ht.le) hmid]
    ring
  rw [hsplit]
  exact ((abs_add_le _ _).trans (add_le_add hnear hfar)).trans_eq (by ring)

end Luce.Section6
