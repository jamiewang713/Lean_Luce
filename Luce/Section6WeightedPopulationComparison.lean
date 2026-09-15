import Luce.Section6WeightedProfileComparison

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem PowerProfile.right_scaled_populationD_comparison {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 1 ≤ t →
    |t*populationD (w n) 1 t -
      t*((∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^beta))/(n : ℝ))| ≤
      K*(t^(-((1+eta)/beta))+1/(n : ℝ)) := by
  have hc := h.2.2.2.1.1
  have hb := h.2.2.2.1.2.1
  have he := h.2.2.2.1.2.2.1
  obtain ⟨C, d, eps, hC, hd, heps, _, hdiff⟩ := h.right_scaled_rate_difference_bound
  obtain ⟨E, hE, hsum⟩ := scaled_power_envelope_average_bound hb he
    (d := c/4) (by positivity)
  obtain ⟨A, hA, hAb⟩ := exponential_le_power (a := (1+eta)/beta) (by positivity) (half_pos hd)
  obtain ⟨B, hB, hBb⟩ := exponential_le_power (a := (1+eta)/beta) (by positivity)
    (half_pos (mul_pos hc (Real.rpow_pos_of_pos heps beta)))
  let R := 2*Real.exp (-1)*(A+B)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨C*E+R, by positivity, ?_⟩
  intro grid w hw n hn t ht1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let s : Fin n → ℝ := samplePoint grid n
  let env : Fin n → ℝ := fun i => (s i)^(beta+eta)*Real.exp (-(((c/4)*t)*(s i)^beta))
  let tail := 2*Real.exp (-1)*(survivalKernel (t/2) d + survivalKernel (t/2) (c*eps^beta))
  have hterm (i : Fin n) : |t*rateKernel t (f (1-s i))-t*rateKernel t (c*(s i)^beta)| ≤
      C*t*env i + tail := by
    have hh := hdiff (s i) (samplePoint_mem grid i) t ht
    have heq : -t*((c/4)*(s i)^beta) = -(((c/4)*t)*(s i)^beta) := by ring
    simpa only [env, tail, survivalKernel, heq, mul_assoc] using hh
  have htail : tail ≤ R*t^(-((1+eta)/beta)) := by
    have h1 : survivalKernel (t/2) d ≤ A*t^(-((1+eta)/beta)) := by
      have heq : -(t/2)*d = -((d/2)*t) := by ring
      simpa only [survivalKernel, heq] using hAb t ht
    have h2 : survivalKernel (t/2) (c*eps^beta) ≤ B*t^(-((1+eta)/beta)) := by
      have heq : -(t/2)*(c*eps^beta) = -((c*eps^beta/2)*t) := by ring
      simpa only [survivalKernel, heq] using hBb t ht
    have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
      (by positivity : 0 ≤ 2*Real.exp (-1))
    exact hh.trans_eq (by dsimp [R]; ring)
  have hbound : |t*populationD (w n) 1 t -
      t*((∑ i : Fin n, rateKernel t (c*(s i)^beta))/(n : ℝ))| ≤
      C*(t*((∑ i, env i)/(n : ℝ))) + tail := by
    rw [populationD_one_eq_reflected_samples grid w f hw n t]
    have heq : t*((∑ i : Fin n, rateKernel t (f (1-s i)))/(n : ℝ)) -
        t*((∑ i : Fin n, rateKernel t (c*(s i)^beta))/(n : ℝ)) =
        (∑ i : Fin n, (t*rateKernel t (f (1-s i))-t*rateKernel t (c*(s i)^beta)))/(n : ℝ) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    change |t*((∑ i : Fin n, rateKernel t (f (1-s i)))/(n : ℝ)) -
      t*((∑ i : Fin n, rateKernel t (c*(s i)^beta))/(n : ℝ))| ≤ _
    rw [heq, abs_div, abs_of_pos hn0]
    calc
      _ ≤ (∑ i : Fin n, |t*rateKernel t (f (1-s i))-t*rateKernel t (c*(s i)^beta)|)/(n : ℝ) :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn0.le
      _ ≤ (∑ i : Fin n, (C*t*env i+tail))/(n : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hterm i) hn0.le
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_div,
          mul_div_cancel_left₀ _ hn0.ne']
        ring
  have henv := hsum grid n hn t ht1
  change t*((∑ i, env i)/(n : ℝ)) ≤ E*(t^(-((1+eta)/beta))+1/(n : ℝ)) at henv
  calc
    _ ≤ C*(t*((∑ i, env i)/(n : ℝ))) + tail := hbound
    _ ≤ C*(E*(t^(-((1+eta)/beta))+1/(n : ℝ))) + R*t^(-((1+eta)/beta)) :=
      add_le_add (mul_le_mul_of_nonneg_left henv hC.le) htail
    _ ≤ _ := by
      have hh := mul_nonneg hR.le (one_div_nonneg.mpr hn0.le)
      nlinarith

end Luce.Section6
