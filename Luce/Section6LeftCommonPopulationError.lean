import Luce.Section6LeftArrivalAsymptotic
import Luce.Section6LeftWeightedAsymptotic

noncomputable section
namespace Luce.Section6

/-- The two left additive population estimates share a constructed
positive saving. Neither an exponent nor a population estimate is assumed. -/
theorem PowerProfile.left_populations_power_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ q K : ℝ, 0 < q ∧ 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → t ≤ 1 →
      (|populationG (w n) t-Real.Gamma (1-1/alpha)*c^(1/alpha)*t^(1/alpha)| ≤
        K*(t^(1/alpha+q)+1/(n : ℝ))) ∧
      (|t*populationD (w n) 1 t-(Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha)| ≤
        K*(t^(1/alpha+q)+1/(n : ℝ))) := by
  have ha := hp.2.2.1.2.1
  obtain ⟨eg, heg, _, hega, G, hG, hGb⟩ := hp.left_populationG_power_error
  obtain ⟨ed, hed, _, heda, D, hD, hDb⟩ := hp.left_scaled_populationD_power_error
  let qg := 1/(alpha-eg)-1/alpha
  let qd := 1/(alpha-ed)-1/alpha
  have hqg : 0 < qg := sub_pos.mpr (one_div_lt_one_div_of_lt (by linarith) (by linarith))
  have hqd : 0 < qd := sub_pos.mpr (one_div_lt_one_div_of_lt (by linarith) (by linarith))
  refine ⟨min qg qd, G+D, lt_min hqg hqd, add_pos hG hD, ?_⟩
  intro grid w hw n hn t ht ht1
  have hpg : 1/alpha+min qg qd ≤ 1/(alpha-eg) := by
    have hh := min_le_left qg qd
    dsimp [qg] at hh
    linarith
  have hpd : 1/alpha+min qg qd ≤ 1/(alpha-ed) := by
    have hh := min_le_right qg qd
    dsimp [qd] at hh
    linarith
  have hg := Real.rpow_le_rpow_of_exponent_ge ht ht1 hpg
  have hd := Real.rpow_le_rpow_of_exponent_ge ht ht1 hpd
  have hE : 0 ≤ t^(1/alpha+min qg qd)+1/(n : ℝ) := by positivity
  constructor
  · exact (hGb grid w hw n hn t ht ht1).trans
      ((mul_le_mul_of_nonneg_left (add_le_add hg (le_refl _)) hG.le).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) hE))
  · exact (hDb grid w hw n hn t ht ht1).trans
      ((mul_le_mul_of_nonneg_left (add_le_add hd (le_refl _)) hD.le).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hG.le) hE))

end Luce.Section6
