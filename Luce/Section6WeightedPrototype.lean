import Luce.Section6PopulationPowerBounds

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem scaled_integral_weighted_power {beta c t : ℝ}
    (hb : 0 < beta) (hc : 0 < c) (ht : 0 < t) :
    t*(∫ s in Ioi (0 : ℝ), rateKernel t (c*s^beta)) =
      (Real.Gamma (1+1/beta)/beta)*c^(-(1/beta))*t^(-(1/beta)) := by
  rw [integral_weighted_power hb hc ht]
  have he : (beta+1)/beta = 1+1/beta := by field_simp
  rw [he, Real.rpow_add (by positivity), Real.rpow_one,
    reciprocal_scaled_rpow hc ht]
  field_simp

theorem weighted_power_tail_bound {beta c t : ℝ}
    (hb : 0 < beta) (hc : 0 < c) (ht : 0 < t) :
    (∫ s in Ioi (1 : ℝ), rateKernel t (c*s^beta)) ≤
      Real.exp (-(c*t)/2)*(∫ s in Ioi (0 : ℝ), rateKernel (t/2) (c*s^beta)) := by
  have hfull := integrableOn_weighted_power hb hc ht
  have hhalf := integrableOn_weighted_power hb hc (half_pos ht)
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  have hterm : ∀ s ∈ Ioi (1 : ℝ), rateKernel t (c*s^beta) ≤
      Real.exp (-(c*t)/2)*rateKernel (t/2) (c*s^beta) := by
    intro s hs
    rw [rateKernel_split_time]
    have henv : survivalKernel (t/2) (c*s^beta) ≤ Real.exp (-(c*t)/2) := by
      apply Real.exp_le_exp.mpr
      have hp := Real.one_le_rpow hs.le hb.le
      nlinarith [mul_nonneg (mul_pos hc ht).le (sub_nonneg.mpr hp)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left henv
      (rateKernel_nonneg (mul_pos hc (Real.rpow_pos_of_pos (zero_lt_one.trans hs) _)).le)
  calc
    _ ≤ ∫ s in Ioi (1 : ℝ), Real.exp (-(c*t)/2)*rateKernel (t/2) (c*s^beta) :=
      setIntegral_mono_on (hfull.mono_set hsub) ((hhalf.mono_set hsub).const_mul _)
        measurableSet_Ioi hterm
    _ = Real.exp (-(c*t)/2)*(∫ s in Ioi (1 : ℝ), rateKernel (t/2) (c*s^beta)) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hhalf
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          exact rateKernel_nonneg (mul_nonneg hc.le (Real.rpow_nonneg hs.le _)))
        (Filter.Eventually.of_forall fun _ hs => hsub hs)) (Real.exp_pos _).le

/-- The weighted power prototype has the exact manuscript coefficient,
with a discretization error O(1/n) after multiplication by t. -/
theorem scaled_weighted_prototype_power_error {beta c eta : ℝ}
    (hb : 0 < beta) (hc : 0 < c) (he : 0 < eta) :
    ∃ K : ℝ, 0 < K ∧ ∀ (grid : SamplingGrid) (n : ℕ), 0 < n →
    ∀ t : ℝ, 1 ≤ t →
    |t*((∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^beta))/(n : ℝ)) -
      (Real.Gamma (1+1/beta)/beta)*c^(-(1/beta))*t^(-(1/beta))| ≤
      K*(t^(-((1+eta)/beta))+1/(n : ℝ)) := by
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  obtain ⟨E, hE, hEb⟩ := exponential_le_power (a := eta/beta) (by positivity) (half_pos hc)
  let W := 2*(Real.Gamma (1+1/beta)/beta)*c^(-(1/beta))/(2 : ℝ)^(-(1/beta))
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨2*Real.exp (-1)+E*W, by positivity, ?_⟩
  intro grid n hn t ht1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have htail := weighted_power_tail_bound hb hc ht
  have hfull := scaled_integral_weighted_power hb hc ht
  have hhalf := scaled_integral_weighted_power hb hc (half_pos ht)
  have hh : t*(∫ s in Ioi (0 : ℝ), rateKernel (t/2) (c*s^beta)) =
      W*t^(-(1/beta)) := by
    rw [Real.div_rpow ht.le (by norm_num)] at hhalf
    calc
      _ = 2*((t/2)*(∫ s in Ioi (0 : ℝ), rateKernel (t/2) (c*s^beta))) := by ring
      _ = _ := by rw [hhalf]; dsimp [W]; ring
  have hprod : t^(-(eta/beta))*t^(-(1/beta)) = t^(-((1+eta)/beta)) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have htail' : t*(∫ s in Ioi (1 : ℝ), rateKernel t (c*s^beta)) ≤
      E*W*t^(-((1+eta)/beta)) := by
    calc
      _ ≤ Real.exp (-(c*t)/2)*(t*(∫ s in Ioi (0 : ℝ), rateKernel (t/2) (c*s^beta))) := by
        simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left htail ht.le
      _ = Real.exp (-((c/2)*t))*(W*t^(-(1/beta))) := by
        rw [hh, show -(c*t)/2 = -((c/2)*t) by ring]
      _ ≤ (E*t^(-(eta/beta)))*(W*t^(-(1/beta))) :=
        mul_le_mul_of_nonneg_right (hEb t ht) (mul_pos hW (Real.rpow_pos_of_pos ht _)).le
      _ = E*W*(t^(-(eta/beta))*t^(-(1/beta))) := by ring
      _ = _ := by rw [hprod]
  have hi := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_weighted_power hb hc ht) zero_le_one
  have hnonneg : 0 ≤ ∫ s in Ioi (1 : ℝ), rateKernel t (c*s^beta) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact rateKernel_nonneg (mul_pos hc (Real.rpow_pos_of_pos (zero_lt_one.trans hs) _)).le
  have hdiff : |t*(∫ s in (0 : ℝ)..1, rateKernel t (c*s^beta)) -
      (Real.Gamma (1+1/beta)/beta)*c^(-(1/beta))*t^(-(1/beta))| =
      t*(∫ s in Ioi (1 : ℝ), rateKernel t (c*s^beta)) := by
    rw [← hfull, ← mul_sub, abs_mul, abs_of_pos ht, ← hi]
    simp only [sub_sub_cancel_left, abs_neg, abs_of_nonneg hnonneg]
  have hquad := mul_le_mul_of_nonneg_left (weighted_power_quadrature grid hn hb hc ht) ht.le
  have hquad' : |t*((∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^beta))/(n : ℝ)) -
      t*(∫ s in (0 : ℝ)..1, rateKernel t (c*s^beta))| ≤ 2*Real.exp (-1)/(n : ℝ) := by
    rw [← mul_sub, abs_mul, abs_of_pos ht]
    exact hquad.trans_eq (by field_simp)
  calc
    _ ≤ |t*((∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^beta))/(n : ℝ)) -
        t*(∫ s in (0 : ℝ)..1, rateKernel t (c*s^beta))| +
        |t*(∫ s in (0 : ℝ)..1, rateKernel t (c*s^beta)) -
        (Real.Gamma (1+1/beta)/beta)*c^(-(1/beta))*t^(-(1/beta))| := abs_sub_le _ _ _
    _ ≤ 2*Real.exp (-1)/(n : ℝ) + E*W*t^(-((1+eta)/beta)) :=
      add_le_add hquad' (by rw [hdiff]; exact htail')
    _ ≤ _ := by
      have h1 := mul_nonneg (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos (-1))).le
        (Real.rpow_pos_of_pos ht (-((1+eta)/beta))).le
      have h2 := mul_nonneg (mul_pos hE hW).le (one_div_nonneg.mpr hn0.le)
      simp only [div_eq_mul_inv, one_mul] at *
      nlinarith

end Luce.Section6
