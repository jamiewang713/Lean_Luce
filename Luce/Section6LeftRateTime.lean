import Luce.Section6SampledRateAsymptotics
import Luce.Section6LeftQuantileAsymptotic
import Luce.Section6RelativeProductError
import Luce.Section6RateTimeConstants

noncomputable section
namespace Luce.Section6

/-- The exact left rate-time product in eq:sp-left-quantile. A common
positive saving is constructed from the rate and time error exponents. -/
theorem PowerProfile.left_rate_time_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ xi C delta M : ℝ, 0 < xi ∧ 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), M ≤ (i.val : ℝ)+1 →
      ((i.val : ℝ)+1)/(n : ℝ) < delta →
      |((w n).rate i*leftQuantileTime (w n) (i.val+1)) /
        (Real.Gamma (1-1/alpha))^(-alpha)-1| ≤
      C*((((i.val : ℝ)+1)/(n : ℝ))^xi+1/((i.val : ℝ)+1)) := by
  have hc := hp.2.2.1.1
  have ha := hp.2.2.1.2.1
  have he := hp.2.2.1.2.2.1
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  obtain ⟨R, dr, hR, hdr, hdr1, hrates⟩ := hp.left_sampled_rate_relative_error
  obtain ⟨zeta, T, dt, M, hz, hT, hdt, hM, htimes⟩ := hp.left_quantile_relative_error
  let xi := min eta zeta
  have hxi : 0 < xi := lt_min he hz
  refine ⟨xi, 2*R*T+R+T, min dr dt, M, hxi, by positivity, lt_min hdr hdt, hM, ?_⟩
  intro grid w hw n i hlarge hsmall
  let m := i.val+1
  let x := (m : ℝ)/(n : ℝ)
  let A := Real.Gamma (1-1/alpha)*c^(1/alpha)
  have hmcast : (m : ℝ) = (i.val : ℝ)+1 := by simp [m]
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hm : 0 < m := by dsimp [m]; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hx : 0 < x := div_pos hmR hnR
  have hxsmall : x < min dr dt := by simpa only [x, hmcast] using hsmall
  have hx1 : x < 1 := (hxsmall.trans_le (min_le_left _ _)).trans hdr1
  have hmn : m < n := by exact_mod_cast (div_lt_one hnR).mp hx1
  have hrate := hrates grid w hw n i (hsmall.trans_le (min_le_left _ _))
  simp only [← hmcast] at hrate
  have htime := htimes grid w hw n m hm hmn (by simpa only [hmcast] using hlarge)
    (hxsmall.trans_le (min_le_right _ _))
  have hscale : x/A = (m : ℝ)/(A*(n : ℝ)) := by dsimp [x]; field_simp
  change |leftQuantileTime (w n) m/((m : ℝ)/(A*(n : ℝ)))^alpha-1| ≤
    T*(x^zeta+1/(m : ℝ)) at htime
  rw [← hscale] at htime
  have hpr : x^eta ≤ x^xi := Real.rpow_le_rpow_of_exponent_ge hx hx1.le (min_le_left _ _)
  have hpt : x^zeta ≤ x^xi := Real.rpow_le_rpow_of_exponent_ge hx hx1.le (min_le_right _ _)
  have hrate' := hrate.trans (mul_le_mul_of_nonneg_left (add_le_add hpr (le_refl (1/(m : ℝ)))) hR.le)
  have htime' := htime.trans (mul_le_mul_of_nonneg_left (add_le_add hpt (le_refl (1/(m : ℝ)))) hT.le)
  have he0 : 0 ≤ x^xi+1/(m : ℝ) := by positivity
  have he2 : x^xi+1/(m : ℝ) ≤ 2 := by
    have hpow : x^xi ≤ 1 := by simpa only [Real.one_rpow] using Real.rpow_le_rpow hx.le hx1.le hxi.le
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hrecip : 1/(m : ℝ) ≤ 1 := (div_le_one hmR).mpr hm1
    linarith
  have hh := relative_product_error hR.le hT.le he0 he2 hrate' htime'
  have hG : 0 < Real.Gamma (1-1/alpha) := by
    apply Real.Gamma_pos_of_pos
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  have hlead : (c*x^(-alpha))*(x/A)^alpha = (Real.Gamma (1-1/alpha))^(-alpha) :=
    left_rate_time_leading hc ha0 hG hx
  have hid : ((w n).rate i/(c*x^(-alpha)))*(leftQuantileTime (w n) m/(x/A)^alpha) =
      ((w n).rate i*leftQuantileTime (w n) m)/(Real.Gamma (1-1/alpha))^(-alpha) := by
    rw [div_mul_div_comm, hlead]
  rw [hid] at hh
  simpa only [x, hmcast] using hh

end Luce.Section6
