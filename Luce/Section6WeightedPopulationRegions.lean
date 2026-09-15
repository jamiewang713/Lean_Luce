import Luce.Section6QuantileComparability
import Luce.Section6RightWeightedAsymptotic
import Luce.Section6LeftWeightedAsymptotic

noncomputable section
namespace Luce.Section6

/-- Uniform two-sided weighted-population bounds throughout the right
asymptotic region. The region constants are derived from the profile. -/
theorem PowerProfile.right_populationD_comparable {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ S M : ℝ, 1 ≤ S ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ s : ℝ, S ≤ s → M ≤ (n : ℝ)*s^(-(1/beta)) →
      let B := (Real.Gamma (1+1/beta)*c^(-(1/beta))/beta)*s^(-1-1/beta)
      B/2 ≤ populationD (w n) 1 s ∧ populationD (w n) 1 s ≤ 2*B := by
  have hc := hp.2.2.2.1.1
  have hb := hp.2.2.2.1.2.1
  have he := hp.2.2.2.1.2.2.1
  obtain ⟨K, hK, hbound⟩ := hp.right_populationD_relative_error
  obtain ⟨delta, M, hd, hM, hsmall⟩ := joint_power_error_small (div_pos he hb) hK
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨max 1 (2/delta), M, le_max_left _ _, hM, ?_⟩
  intro grid w hw n hn s hs hm
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  have hsd : 1/s < delta := by
    apply (div_lt_iff₀ hs0).mpr
    have hh := (div_le_iff₀ hd).mp ((le_max_right _ _).trans hs)
    nlinarith
  have hh := hsmall (1/s) ((n : ℝ)*s^(-(1/beta))) (one_div_pos.mpr hs0) hsd hm
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow] at hh
  have herr := (hbound grid w hw n hn s hs1).trans hh
  apply half_relative_error_bounds _ herr
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  positivity

theorem PowerProfile.left_populationD_comparable {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ S M : ℝ, 0 < S ∧ S ≤ 1 ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ s : ℝ, 0 < s → s ≤ S → M ≤ (n : ℝ)*s^(1/alpha) →
      let B := (Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*s^(1/alpha-1)
      B/2 ≤ populationD (w n) 1 s ∧ populationD (w n) 1 s ≤ 2*B := by
  have hc := hp.2.2.1.1
  have ha := hp.2.2.1.2.1
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  obtain ⟨zeta, K, hzeta, hK, hbound⟩ := hp.left_populationD_relative_error
  obtain ⟨delta, M, hd, hM, hsmall⟩ := joint_power_error_small hzeta hK
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨min 1 (delta/2), M, lt_min zero_lt_one (half_pos hd), min_le_left _ _, hM, ?_⟩
  intro grid w hw n hn s hs0 hs hm
  have hs1 : s ≤ 1 := hs.trans (min_le_left _ _)
  have hsd : s < delta := (hs.trans (min_le_right _ _)).trans_lt (by linarith)
  have herr := (hbound grid w hw n hn s hs0 hs1).trans
    (hsmall s ((n : ℝ)*s^(1/alpha)) hs0 hsd hm)
  apply half_relative_error_bounds _ herr
  have hG : 0 < Real.Gamma (1-1/alpha) := by
    apply Real.Gamma_pos_of_pos
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  positivity

end Luce.Section6
