import Luce.Section6SmallTimePopulation
import Luce.Section6RightPopulationAsymptotic

noncomputable section
namespace Luce.Section6

theorem populationH_le_uniform_rate {n : ℕ} (hn : 0 < n) (w : Weights n)
    {d t : ℝ} (ht : 0 ≤ t) (hbound : ∀ i, d ≤ w.rate i) :
    populationH w t ≤ Real.exp (-(d*t)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold populationH
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ _i : Fin n, Real.exp (-(d*t)) := Finset.sum_le_sum fun i _ => by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (hbound i) ht
      nlinarith
    _ = _ := by simp; ring

/-- Uniform large-time survivor control, with no extra endpoint assumption. -/
theorem PowerProfile.large_time_populationH {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (he : 0 < eps) :
    ∃ T N : ℝ, 1 ≤ T ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) → populationH (w n) T ≤ eps := by
  cases right with
  | finite c =>
    obtain ⟨d, hd, hb⟩ := hp.global_lower_of_right_finite
    obtain ⟨C, hC, hdecay⟩ := exponential_le_power (a := 1) zero_le_one hd
    let T := max 1 (C/eps)
    have hT : 0 < T := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨T, 1, le_max_left _ _, zero_lt_one, ?_⟩
    intro grid w hw n hn _
    have hbound : ∀ i, d ≤ (w n).rate i := by
      intro i
      rw [hw n i]
      exact hb _ (samplePoint_mem grid i)
    have hsmall : C/T ≤ eps := by
      apply (div_le_iff₀ hT).mpr
      have hh := mul_le_mul_of_nonneg_left (le_max_right 1 (C/eps)) he.le
      have heq : eps*(C/eps) = C := by field_simp
      rw [heq] at hh
      exact hh
    calc
      _ ≤ Real.exp (-(d*T)) := populationH_le_uniform_rate hn (w n) hT.le hbound
      _ ≤ C*T^(-(1 : ℝ)) := hdecay T hT
      _ = C/T := by rw [Real.rpow_neg hT.le, Real.rpow_one]; rfl
      _ ≤ eps := hsmall
  | power c beta eta =>
    have hc := hp.2.2.2.1.1
    have hb := hp.2.2.2.1.2.1
    have he' := hp.2.2.2.1.2.2.1
    have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
    obtain ⟨K, hK, herr⟩ := hp.right_populationH_power_error
    obtain ⟨s, N, hs, hs1, hN, hsmall⟩ := two_power_small_time
      (mul_pos hG (Real.rpow_pos_of_pos hc (-(1/beta)))) hK
      (one_div_pos.mpr hb) (show 0 < (1+eta)/beta by positivity) he
    have hT : 0 < 1/s := one_div_pos.mpr hs
    have hT1 : 1 ≤ 1/s := (le_div_iff₀ hs).mpr (by simpa using hs1)
    have hpow (p : ℝ) : (1/s)^(-p) = s^p := by
      rw [one_div, ← Real.rpow_neg_eq_inv_rpow, neg_neg]
    refine ⟨1/s, N, hT1, hN, ?_⟩
    intro grid w hw n hn hlarge
    have hh := (abs_le.mp (herr grid w hw n hn (1/s) hT1)).2
    rw [reciprocal_scaled_rpow hc hT, hpow, hpow] at hh
    have hh' := hsmall (n : ℝ) hlarge
    nlinarith

theorem PowerProfile.interior_quantile_time_bounds {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (he : 0 < eps) :
    ∃ s T N : ℝ, 0 < s ∧ 1 ≤ T ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ x : ℝ, eps ≤ x → x ≤ 1-eps →
      (s ≤ arrivalQuantile (w n) x ∧ arrivalQuantile (w n) x ≤ T) ∧
      (s ≤ survivorQuantile (w n) x ∧ survivorQuantile (w n) x ≤ T) := by
  obtain ⟨s, Nl, hs, hNl, hl⟩ := hp.interior_quantile_time_lower he
  obtain ⟨T, Nr, hT, hNr, hr⟩ := hp.large_time_populationH he
  refine ⟨s, T, max Nl Nr, hs, hT, hNl.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge x hx hx'
  have hlo := hl grid w hw n hn ((le_max_left _ _).trans hlarge) x hx hx'
  have hhi := hr grid w hw n hn ((le_max_right _ _).trans hlarge)
  have hx0 : 0 < x := he.trans_le hx
  have hx1 : x < 1 := by linarith
  refine ⟨⟨hlo.1, ?_⟩, ⟨hlo.2, ?_⟩⟩
  · apply (arrivalQuantile_le_iff hn (w n) ⟨hx0.le, hx1⟩ T).mpr
    rw [populationG_eq_one_sub_H hn (w n)]
    linarith
  · exact (survivorQuantile_le_iff hn (w n) ⟨hx0, hx1.le⟩ T).mpr (hhi.trans hx)

end Luce.Section6
