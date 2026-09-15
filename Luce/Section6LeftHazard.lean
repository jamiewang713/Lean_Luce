import Luce.Section6LeftQuantileWeighted
import Luce.Section6LeftRateTime
import Luce.Section6JointErrorCutoffs

noncomputable section
namespace Luce.Section6

/-- The left hazard in eq:sp-left-quantile with the exact coefficient.
Both relative errors and denominator control are derived, not assumed. -/
theorem PowerProfile.left_quantile_hazard_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ xi C delta M : ℝ, 0 < xi ∧ 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), M ≤ (i.val : ℝ)+1 →
      ((i.val : ℝ)+1)/(n : ℝ) < delta →
      let t := leftQuantileTime (w n) (i.val+1)
      |((w n).rate i/((n : ℝ)*populationD (w n) 1 t)) /
        (alpha*(Real.Gamma (1-1/alpha))^(-alpha)/((i.val : ℝ)+1))-1| ≤
      C*((((i.val : ℝ)+1)/(n : ℝ))^xi+1/((i.val : ℝ)+1)) := by
  have ha := hp.2.2.1.2.1
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  obtain ⟨xr, R, dr, Mr, hxr, hR, hdr, hMr, hrate⟩ := hp.left_rate_time_relative_error
  obtain ⟨xd, D, dd, Md, hxd, hD, hdd, hMd, hdenom⟩ := hp.left_quantile_scaledD_relative_error
  let xi := min xr xd
  have hxi : 0 < xi := lt_min hxr hxd
  obtain ⟨ds, Ms, hds, hMs, hsmallError⟩ := joint_power_error_small hxi hD
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨xi, 2*(R+D), min 1 (min dr (min dd ds)), max Mr (max Md Ms), hxi, by positivity,
    lt_min zero_lt_one (lt_min hdr (lt_min hdd hds)), hMr.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n i hlarge hsmall
  let m := i.val+1
  let x := (m : ℝ)/(n : ℝ)
  let t := leftQuantileTime (w n) m
  have hmcast : (m : ℝ) = (i.val : ℝ)+1 := by simp [m]
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hm : 0 < m := by dsimp [m]; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hx : 0 < x := div_pos hmR hnR
  have hsmall' : x < min 1 (min dr (min dd ds)) := by simpa only [x, hmcast] using hsmall
  have hlarge' : max Mr (max Md Ms) ≤ (m : ℝ) := by simpa only [hmcast] using hlarge
  have hx1 : x < 1 := hsmall'.trans_le (min_le_left _ _)
  have hmn : m < n := by exact_mod_cast (div_lt_one hnR).mp hx1
  have hcut : x < min dr (min dd ds) := hsmall'.trans_le (min_le_right _ _)
  have hr := hrate grid w hw n i ((le_max_left _ _).trans hlarge)
    (by simpa only [x, hmcast] using (hcut.trans_le (min_le_left _ _)))
  simp only [← hmcast] at hr
  have hd := hdenom grid w hw n m hm hmn
    ((le_max_left _ _).trans ((le_max_right _ _).trans hlarge'))
    ((hcut.trans_le (min_le_right _ _)).trans_le (min_le_left _ _))
  have hpr : x^xr ≤ x^xi := Real.rpow_le_rpow_of_exponent_ge hx hx1.le (min_le_left _ _)
  have hpd : x^xd ≤ x^xi := Real.rpow_le_rpow_of_exponent_ge hx hx1.le (min_le_right _ _)
  have hr' := hr.trans (mul_le_mul_of_nonneg_left (add_le_add hpr (le_refl (1/(m : ℝ)))) hR.le)
  have hd' := hd.trans (mul_le_mul_of_nonneg_left (add_le_add hpd (le_refl (1/(m : ℝ)))) hD.le)
  have hs := hsmallError x (m : ℝ) hx
    ((hcut.trans_le (min_le_right _ _)).trans_le (min_le_right _ _))
    ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge'))
  have hh := relative_quotient_error hR.le hD.le (by positivity : 0 ≤ x^xi+1/(m : ℝ)) hr' hd' hs
  have ht : 0 < t := (leftQuantileTime_spec (w n) hm hmn).1
  have hpop : 0 < populationD (w n) 1 t := populationD_pos hn (w n) 1 t
  have hG : 0 < Real.Gamma (1-1/alpha) := by
    apply Real.Gamma_pos_of_pos
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  have hq : 0 < (Real.Gamma (1-1/alpha))^(-alpha) := Real.rpow_pos_of_pos hG _
  have hid : (((w n).rate i*t)/(Real.Gamma (1-1/alpha))^(-alpha)) /
      (alpha*t*populationD (w n) 1 t/x) =
      ((w n).rate i/((n : ℝ)*populationD (w n) 1 t)) /
        (alpha*(Real.Gamma (1-1/alpha))^(-alpha)/(m : ℝ)) := by
    dsimp [x]
    field_simp
  rw [hid] at hh
  simpa only [x, hmcast] using hh

end Luce.Section6
