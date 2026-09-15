import Luce.Section6SampledRateAsymptotics

noncomputable section
namespace Luce.Section6

/-- A relative error gives a uniform power envelope even at the first label.
No extra lower cutoff on the label depth is required. -/
theorem relative_error_power_upper {rate c x m p eta C : ℝ}
    (hc : 0 < c) (hx : 0 < x) (hx1 : x ≤ 1) (hm : 1 ≤ m)
    (heta : 0 ≤ eta) (hC : 0 ≤ C)
    (herr : |rate/(c*x^p)-1| ≤ C*(x^eta+1/m)) :
    rate ≤ ((1+2*C)*c)*x^p := by
  have hxpow : x^eta ≤ 1 := Real.rpow_le_one hx.le hx1 heta
  have hminv : 1/m ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < m)).mpr hm
  have he := (abs_le.mp herr).2
  have hb : rate/(c*x^p) ≤ 1+2*C := by nlinarith
  have hden : 0 < c*x^p := mul_pos hc (Real.rpow_pos_of_pos hx _)
  have hh := (div_le_iff₀ hden).mp hb
  nlinarith only [hh]

theorem PowerProfile.left_sampled_rate_upper {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ K delta : ℝ, 0 < K ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), ((i.val : ℝ)+1)/(n : ℝ) < delta →
      (w n).rate i ≤ K*((((i.val : ℝ)+1)/(n : ℝ))^(-alpha)) := by
  obtain ⟨C, delta, hC, hd, hd1, herr⟩ := hp.left_sampled_rate_relative_error
  have hc : 0 < c := hp.2.2.1.1
  refine ⟨(1+2*C)*c, delta, mul_pos (by linarith) hc, hd, hd1, ?_⟩
  intro grid w hw n i hi
  have hm : 1 ≤ (i.val : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  exact relative_error_power_upper hc (div_pos (by linarith) hn) (hi.trans hd1).le hm
    hp.2.2.1.2.2.1.le hC.le (herr grid w hw n i hi)

theorem PowerProfile.right_sampled_rate_upper {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ K delta : ℝ, 0 < K ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < delta →
      (w n).rate i ≤ K*(((terminalDepth i : ℝ)/(n : ℝ))^beta) := by
  obtain ⟨C, delta, hC, hd, hd1, herr⟩ := hp.right_sampled_rate_relative_error
  have hc : 0 < c := hp.2.2.2.1.1
  refine ⟨(1+2*C)*c, delta, mul_pos (by linarith) hc, hd, hd1, ?_⟩
  intro grid w hw n i hi
  have hm : (1 : ℝ) ≤ terminalDepth i := by exact_mod_cast terminalDepth_pos i
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  exact relative_error_power_upper hc (div_pos (by linarith) hn) (hi.trans hd1).le hm
    hp.2.2.2.1.2.2.1.le hC.le (herr grid w hw n i hi)

end Luce.Section6
