import Luce.Section6SampledRateAsymptotics
import Luce.Section6RightQuantileAsymptotic
import Luce.Section6RelativeProductError
import Luce.Section6RateTimeConstants

noncomputable section
namespace Luce.Section6

/-- The exact right rate-time product in eq:sp-right-quantile. -/
theorem PowerProfile.right_rate_time_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ C delta M : ℝ, 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), M ≤ (terminalDepth i : ℝ) →
      (terminalDepth i : ℝ)/(n : ℝ) < delta →
      |((w n).rate i*rightQuantileTime (w n) (terminalDepth i)) /
        (Real.Gamma (1+1/beta))^beta-1| ≤
      C*(((terminalDepth i : ℝ)/(n : ℝ))^eta+1/(terminalDepth i : ℝ)) := by
  have hc := hp.2.2.2.1.1
  have hb := hp.2.2.2.1.2.1
  have he := hp.2.2.2.1.2.2.1
  obtain ⟨R, dr, hR, hdr, hdr1, hrates⟩ := hp.right_sampled_rate_relative_error
  obtain ⟨T, dt, M, hT, hdt, hM, htimes⟩ := hp.right_quantile_relative_error
  refine ⟨2*R*T+R+T, min dr dt, M, by positivity, lt_min hdr hdt, hM, ?_⟩
  intro grid w hw n i hlarge hsmall
  let m := terminalDepth i
  let x := (m : ℝ)/(n : ℝ)
  let A := Real.Gamma (1+1/beta)*c^(-(1/beta))
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hm : 0 < m := terminalDepth_pos i
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hx : 0 < x := div_pos hmR hnR
  have hx1 : x < 1 := (hsmall.trans_le (min_le_left _ _)).trans hdr1
  have hmn : m < n := by exact_mod_cast (div_lt_one hnR).mp hx1
  have hrate := hrates grid w hw n i (hsmall.trans_le (min_le_left _ _))
  have htime := htimes grid w hw n m hm hmn hlarge (hsmall.trans_le (min_le_right _ _))
  have hscale : A/x = A*(n : ℝ)/(m : ℝ) := by dsimp [x]; field_simp
  change |rightQuantileTime (w n) m/(A*(n : ℝ)/(m : ℝ))^beta-1| ≤
    T*(x^eta+1/(m : ℝ)) at htime
  rw [← hscale] at htime
  have he0 : 0 ≤ x^eta+1/(m : ℝ) := by positivity
  have he2 : x^eta+1/(m : ℝ) ≤ 2 := by
    have hpow : x^eta ≤ 1 := by simpa only [Real.one_rpow] using Real.rpow_le_rpow hx.le hx1.le he.le
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hrecip : 1/(m : ℝ) ≤ 1 := (div_le_one hmR).mpr hm1
    linarith
  have hh := relative_product_error hR.le hT.le he0 he2 hrate htime
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  have hlead : (c*x^beta)*(A/x)^beta = (Real.Gamma (1+1/beta))^beta :=
    right_rate_time_leading hc hb hG hx
  have hid : ((w n).rate i/(c*x^beta))*(rightQuantileTime (w n) m/(A/x)^beta) =
      ((w n).rate i*rightQuantileTime (w n) m)/(Real.Gamma (1+1/beta))^beta := by
    rw [div_mul_div_comm, hlead]
  rw [hid] at hh
  exact hh

end Luce.Section6
