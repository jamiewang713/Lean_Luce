import Luce.Section6RightQuantileWeighted
import Luce.Section6RightRateTime
import Luce.Section6JointErrorCutoffs

noncomputable section
namespace Luce.Section6

/-- The right quantile hazard in eq:sp-right-quantile. The weighted
denominator and its small relative error are proved from the profile. -/
theorem PowerProfile.right_quantile_hazard_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ C delta M : ℝ, 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), M ≤ (terminalDepth i : ℝ) →
      (terminalDepth i : ℝ)/(n : ℝ) < delta →
      let t := rightQuantileTime (w n) (terminalDepth i)
      |((w n).rate i/((n : ℝ)*populationD (w n) 1 t)) /
        (beta*(Real.Gamma (1+1/beta))^beta/(terminalDepth i : ℝ))-1| ≤
      C*(((terminalDepth i : ℝ)/(n : ℝ))^eta+1/(terminalDepth i : ℝ)) := by
  have hb := hp.2.2.2.1.2.1
  have he := hp.2.2.2.1.2.2.1
  obtain ⟨R, dr, Mr, hR, hdr, hMr, hrate⟩ := hp.right_rate_time_relative_error
  obtain ⟨D, dd, Md, hD, hdd, hMd, hdenom⟩ := hp.right_quantile_scaledD_relative_error
  obtain ⟨ds, Ms, hds, hMs, hsmallError⟩ := joint_power_error_small he hD
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨2*(R+D), min 1 (min dr (min dd ds)), max Mr (max Md Ms), by positivity,
    lt_min zero_lt_one (lt_min hdr (lt_min hdd hds)), hMr.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n i hlarge hsmall
  let m := terminalDepth i
  let x := (m : ℝ)/(n : ℝ)
  let t := rightQuantileTime (w n) m
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hm : 0 < m := terminalDepth_pos i
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hx : 0 < x := div_pos hmR hnR
  have hx1 : x < 1 := hsmall.trans_le (min_le_left _ _)
  have hmn : m < n := by exact_mod_cast (div_lt_one hnR).mp hx1
  have hcut : x < min dr (min dd ds) := hsmall.trans_le (min_le_right _ _)
  have hr := hrate grid w hw n i ((le_max_left _ _).trans hlarge)
    (hcut.trans_le (min_le_left _ _))
  have hd := hdenom grid w hw n m hm hmn
    ((le_max_left _ _).trans ((le_max_right _ _).trans hlarge))
    ((hcut.trans_le (min_le_right _ _)).trans_le (min_le_left _ _))
  have hs := hsmallError x (m : ℝ) hx
    ((hcut.trans_le (min_le_right _ _)).trans_le (min_le_right _ _))
    ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have hh := relative_quotient_error hR.le hD.le (by positivity : 0 ≤ x^eta+1/(m : ℝ)) hr hd hs
  have ht : 0 < t := (rightQuantileTime_spec (w n) hm hmn).1
  have hpop : 0 < populationD (w n) 1 t := populationD_pos hn (w n) 1 t
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  have hq : 0 < (Real.Gamma (1+1/beta))^beta := Real.rpow_pos_of_pos hG _
  have hid : (((w n).rate i*t)/(Real.Gamma (1+1/beta))^beta) /
      (beta*t*populationD (w n) 1 t/x) =
      ((w n).rate i/((n : ℝ)*populationD (w n) 1 t)) /
        (beta*(Real.Gamma (1+1/beta))^beta/(m : ℝ)) := by
    dsimp [x]
    field_simp
  rw [hid] at hh
  exact hh

end Luce.Section6
