import Luce.Section6JointErrorCutoffs
import Luce.Section6RightQuantileAsymptotic
import Luce.Section6LeftQuantileAsymptotic

noncomputable section
namespace Luce.Section6

theorem half_relative_error_bounds {t T : ℝ} (hT : 0 < T)
    (h : |t/T-1| ≤ 1/2) : T/2 ≤ t ∧ t ≤ 2*T := by
  have hh := abs_le.mp h
  constructor
  · have hlo : (1/2 : ℝ) ≤ t/T := by linarith [hh.1]
    have hmul := (le_div_iff₀ hT).mp hlo
    linarith
  · have hhi : t/T ≤ 2 := by linarith [hh.2]
    exact (div_le_iff₀ hT).mp hhi

/-- Coarse time comparison derived from the quantitative theorem,
with cutoffs depending only on the original profile. -/
theorem PowerProfile.right_quantile_comparable {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ delta M : ℝ, 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let T := ((Real.Gamma (1+1/beta)*c^(-(1/beta)))*(n : ℝ)/(m : ℝ))^beta
      T/2 ≤ rightQuantileTime (w n) m ∧ rightQuantileTime (w n) m ≤ 2*T := by
  obtain ⟨C, d, M, hC, hd, hM, herr⟩ := hp.right_quantile_relative_error
  obtain ⟨d', M', hd', hM', hsmall⟩ := joint_power_error_small hp.2.2.2.1.2.2.1 hC
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨min d d', max M M', lt_min hd hd', hM.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n m hm hmn hlarge hxsmall
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (hm.trans hmn)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hh := herr grid w hw n m hm hmn ((le_max_left _ _).trans hlarge)
    (hxsmall.trans_le (min_le_left _ _))
  have he := hsmall ((m : ℝ)/(n : ℝ)) (m : ℝ) (div_pos hmR hnR)
    (hxsmall.trans_le (min_le_right _ _)) ((le_max_right _ _).trans hlarge)
  apply half_relative_error_bounds _ (hh.trans he)
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity [hp.2.2.2.1.2.1])
  have hc := hp.2.2.2.1.1
  positivity

theorem PowerProfile.left_quantile_comparable {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ delta M : ℝ, 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let T := ((m : ℝ)/((Real.Gamma (1-1/alpha)*c^(1/alpha))*(n : ℝ)))^alpha
      T/2 ≤ leftQuantileTime (w n) m ∧ leftQuantileTime (w n) m ≤ 2*T := by
  obtain ⟨xi, C, d, M, hxi, hC, hd, hM, herr⟩ := hp.left_quantile_relative_error
  obtain ⟨d', M', hd', hM', hsmall⟩ := joint_power_error_small hxi hC
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨min d d', max M M', lt_min hd hd', hM.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n m hm hmn hlarge hxsmall
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (hm.trans hmn)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hh := herr grid w hw n m hm hmn ((le_max_left _ _).trans hlarge)
    (hxsmall.trans_le (min_le_left _ _))
  have he := hsmall ((m : ℝ)/(n : ℝ)) (m : ℝ) (div_pos hmR hnR)
    (hxsmall.trans_le (min_le_right _ _)) ((le_max_right _ _).trans hlarge)
  apply half_relative_error_bounds _ (hh.trans he)
  have ha := hp.2.2.1.2.1
  have hc := hp.2.2.1.1
  have hG : 0 < Real.Gamma (1-1/alpha) := by
    apply Real.Gamma_pos_of_pos
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  positivity

end Luce.Section6
