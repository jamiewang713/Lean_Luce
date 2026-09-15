import Luce.Section6WindowMoments
import Luce.Section6RightPopulationWindow
import Luce.Section6LeftPopulationWindow
import Luce.Section6RightQuantileWeighted
import Luce.Section6LeftQuantileWeighted

noncomputable section
namespace Luce.Section6

/-- Both moment estimates of eq:sp-rough-moments at the right endpoint. -/
theorem PowerProfile.right_quantile_moments {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ a C delta M : ℝ, 0 < a ∧ 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := rightQuantileTime (w n) m
      ∀ s : ℝ, t/4 ≤ s → s ≤ 4*t →
        a*(m : ℝ)/t ≤ (n : ℝ)*populationD (w n) 1 s ∧
        (n : ℝ)*populationD (w n) 1 s ≤ C*(m : ℝ)/t ∧
        (n : ℝ)*populationD (w n) 2 s ≤ C*(m : ℝ)/t^2 := by
  have hc := hp.2.2.2.1.1
  have hb := hp.2.2.2.1.2.1
  have he := hp.2.2.2.1.2.2.1
  have hr : -1-1/beta ≤ 0 := by have := one_div_pos.mpr hb; linarith
  obtain ⟨a, C, ha, hC, hmoments⟩ := population_moments_from_power_window hb hr
  obtain ⟨dw, Mw, hdw, hMw, hwindow⟩ := hp.right_populationD_quantile_window
  obtain ⟨K, dn, Mn, hK, hdn, hMn, hnorm⟩ := hp.right_quantile_scaledD_relative_error
  obtain ⟨de, Me, hde, hMe, herror⟩ := joint_power_error_small he hK (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨a, C, min dw (min dn de), max Mw (max Mn Me), ha, hC,
    lt_min hdw (lt_min hdn hde), hMw.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  have hn : 0 < n := hm.trans hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hwin := hwindow grid w hw n m hm hmn ((le_max_left _ _).trans hlarge)
    (hsmall.trans_le (min_le_left _ _))
  have hcen := hnorm grid w hw n m hm hmn
    ((le_max_left _ _).trans ((le_max_right _ _).trans hlarge))
    ((hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _))
  have hsmallE := herror ((m : ℝ)/(n : ℝ)) (m : ℝ) (div_pos hmR hnR)
    ((hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _))
    ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have ht := (rightQuantileTime_spec (w n) hm hmn).1
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  have hB : 0 < Real.Gamma (1+1/beta)*c^(-(1/beta))/beta := by positivity
  exact hmoments n (w n) (m : ℝ) (rightQuantileTime (w n) m) _ hn hmR ht hB hwin (hcen.trans hsmallE)

/-- Both moment estimates of eq:sp-rough-moments at the left endpoint. -/
theorem PowerProfile.left_quantile_moments {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ a C delta M : ℝ, 0 < a ∧ 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := leftQuantileTime (w n) m
      ∀ s : ℝ, t/4 ≤ s → s ≤ 4*t →
        a*(m : ℝ)/t ≤ (n : ℝ)*populationD (w n) 1 s ∧
        (n : ℝ)*populationD (w n) 1 s ≤ C*(m : ℝ)/t ∧
        (n : ℝ)*populationD (w n) 2 s ≤ C*(m : ℝ)/t^2 := by
  have hc := hp.2.2.1.1
  have ha := hp.2.2.1.2.1
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  have hg : 0 < 1-1/alpha := by
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  have hr : 1/alpha-1 ≤ 0 := by linarith
  obtain ⟨a, C, ha', hC, hmoments⟩ := population_moments_from_power_window ha0 hr
  obtain ⟨dw, Mw, hdw, hMw, hwindow⟩ := hp.left_populationD_quantile_window
  obtain ⟨xi, K, dn, Mn, hxi, hK, hdn, hMn, hnorm⟩ := hp.left_quantile_scaledD_relative_error
  obtain ⟨de, Me, hde, hMe, herror⟩ := joint_power_error_small hxi hK (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨a, C, min dw (min dn de), max Mw (max Mn Me), ha', hC,
    lt_min hdw (lt_min hdn hde), hMw.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  have hn : 0 < n := hm.trans hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hwin := hwindow grid w hw n m hm hmn ((le_max_left _ _).trans hlarge)
    (hsmall.trans_le (min_le_left _ _))
  have hcen := hnorm grid w hw n m hm hmn
    ((le_max_left _ _).trans ((le_max_right _ _).trans hlarge))
    ((hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _))
  have hsmallE := herror ((m : ℝ)/(n : ℝ)) (m : ℝ) (div_pos hmR hnR)
    ((hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _))
    ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have ht := (leftQuantileTime_spec (w n) hm hmn).1
  have hG := Real.Gamma_pos_of_pos hg
  have hB : 0 < Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha := by positivity
  exact hmoments n (w n) (m : ℝ) (leftQuantileTime (w n) m) _ hn hmR ht hB hwin (hcen.trans hsmallE)

end Luce.Section6
