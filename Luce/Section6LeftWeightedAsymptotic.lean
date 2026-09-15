import Luce.Section6FastWeightedPopulationComparison

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem time_mul_fast_weighted_power {t : ℝ} (ht : 0 < t) (alpha : ℝ) :
    t*t^(1/alpha-1) = t^(1/alpha) := by
  conv_lhs => lhs; rw [← Real.rpow_one t]
  rw [← Real.rpow_add ht]
  congr 1
  ring

theorem PowerProfile.left_scaled_populationD_power_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) :
    ∃ eta' : ℝ, 0 < eta' ∧ eta' < eta ∧ eta' < alpha-1 ∧
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → t ≤ 1 →
    |t*populationD (w n) 1 t -
      (Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha)| ≤
      K*(t^(1/(alpha-eta'))+1/(n : ℝ)) := by
  have hc := h.2.2.1.1
  have ha := h.2.2.1.2.1
  obtain ⟨eta', he, heeta, healpha, C, hC, hcomp⟩ := h.left_scaled_populationD_comparison
  have hq : 1 < alpha-eta' := by linarith
  have hq0 : 0 < alpha-eta' := zero_lt_one.trans hq
  let B := c/(alpha-1)
  let E := 2*Real.exp (-1)
  have hB : 0 < B := div_pos hc (sub_pos.mpr ha)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨eta', he, heeta, healpha, C+E+B, by positivity, ?_⟩
  intro grid w hw n hn t ht ht1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsmall : t ≤ t^(1/(alpha-eta')) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1
      ((div_le_one hq0).mpr hq.le)
  have hp := mul_le_mul_of_nonneg_left (fast_weighted_prototype_error grid hn ha hc ht) ht.le
  have hp' : |t*((∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^(-alpha)))/(n : ℝ)) -
      (Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha)| ≤
      E/(n : ℝ)+B*t := by
    have hlead : (Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha) =
        t*((Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha-1)) := by
      rw [mul_left_comm t, time_mul_fast_weighted_power ht alpha]
    rw [hlead, ← mul_sub, abs_mul, abs_of_pos ht]
    exact hp.trans_eq (by dsimp [E, B]; field_simp)
  calc
    _ ≤ |t*populationD (w n) 1 t -
        t*((∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^(-alpha)))/(n : ℝ))| +
        |t*((∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^(-alpha)))/(n : ℝ)) -
        (Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha)| := abs_sub_le _ _ _
    _ ≤ C*(t^(1/(alpha-eta'))+1/(n : ℝ))+(E/(n : ℝ)+B*t) :=
      add_le_add (hcomp grid w hw n hn t ht ht1) hp'
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hsmall hB.le
      have h1 := mul_nonneg hE.le (Real.rpow_pos_of_pos ht (1/(alpha-eta'))).le
      have h2 := mul_nonneg hB.le (one_div_nonneg.mpr hn0.le)
      simp only [div_eq_mul_inv, one_mul] at *
      nlinarith

/-- The left weighted-population assertion with the exact Gamma constant
and an error exponent proved to be positive from the original expansion. -/
theorem PowerProfile.left_populationD_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) :
    ∃ zeta K : ℝ, 0 < zeta ∧ 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → t ≤ 1 →
    |populationD (w n) 1 t /
        ((Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha-1)) - 1| ≤
      K*(t^zeta+1/((n : ℝ)*t^(1/alpha))) := by
  have hc := h.2.2.1.1
  have ha := h.2.2.1.2.1
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  have hg : 0 < 1-1/alpha := by
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  let B := Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha
  have hB : 0 < B := div_pos (mul_pos (Real.Gamma_pos_of_pos hg) (Real.rpow_pos_of_pos hc _)) ha0
  obtain ⟨eta', he, _, healpha, C, hC, hbound⟩ := h.left_scaled_populationD_power_error
  have hq0 : 0 < alpha-eta' := by linarith
  let zeta := 1/(alpha-eta')-1/alpha
  have hz : 0 < zeta := sub_pos.mpr (one_div_lt_one_div_of_lt hq0 (by linarith))
  refine ⟨zeta, C/B, hz, div_pos hC hB, ?_⟩
  intro grid w hw n hn t ht ht1
  have hp : 0 < t^(1/alpha) := Real.rpow_pos_of_pos ht _
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have herr := hbound grid w hw n hn t ht ht1
  change |t*populationD (w n) 1 t - B*t^(1/alpha)| ≤ _ at herr
  have hprod : t^zeta*t^(1/alpha) = t^(1/(alpha-eta')) := by
    rw [← Real.rpow_add ht]
    congr 1
    dsimp [zeta]
    ring
  have hratio : populationD (w n) 1 t / (B*t^(1/alpha-1)) =
      (t*populationD (w n) 1 t)/(B*t^(1/alpha)) := by
    rw [← time_mul_fast_weighted_power ht alpha]
    field_simp
  change |populationD (w n) 1 t / (B*t^(1/alpha-1)) - 1| ≤ _
  rw [hratio, div_sub_one (mul_pos hB hp).ne', abs_div, abs_of_pos (mul_pos hB hp)]
  apply (div_le_iff₀ (mul_pos hB hp)).mpr
  calc
    _ ≤ C*(t^(1/(alpha-eta'))+1/(n : ℝ)) := herr
    _ = _ := by rw [← hprod]; field_simp

end Luce.Section6
