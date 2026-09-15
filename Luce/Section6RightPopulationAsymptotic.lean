import Luce.Section6PopulationPowerBounds

noncomputable section
namespace Luce.Section6

/-- A uniform additive version of the manuscript's right-survivor population
asymptotic, valid for both sampling grids and every n>0 and t≥1. -/
theorem PowerProfile.right_populationH_power_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 1 ≤ t →
    |populationH (w n) t - (1/(c*t))^(1/beta)*Real.Gamma (1+1/beta)| ≤
      K*(t^(-((1+eta)/beta)) + 1/(n : ℝ)) := by
  have hc : 0 < c := h.2.2.2.1.1
  have hb : 0 < beta := h.2.2.2.1.2.1
  have he : 0 < eta := h.2.2.2.1.2.2.1
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  obtain ⟨C, d, eps, hC, hd, heps, _, herr⟩ := h.right_populationH_error
  obtain ⟨A, hA, hAb⟩ := exponential_le_power (a := (1+eta)/beta) (by positivity) hd
  obtain ⟨B, hB, hBb⟩ := exponential_le_power (a := (1+eta)/beta) (by positivity)
    (mul_pos hc (Real.rpow_pos_of_pos heps beta))
  obtain ⟨E, hE, hEb⟩ := exponential_le_power (a := eta/beta) (by positivity)
    (half_pos hc)
  let U := (c/4)^(-((beta+eta)/beta))
  let V := (c/4)^(-(1/beta))*Real.Gamma (1+1/beta)
  let W := (c/2)^(-(1/beta))*Real.Gamma (1+1/beta)
  have hU : 0 < U := Real.rpow_pos_of_pos (by positivity) _
  have hV : 0 < V := mul_pos (Real.rpow_pos_of_pos (by positivity) _) hG
  have hW : 0 < W := mul_pos (Real.rpow_pos_of_pos (half_pos hc) _) hG
  let KP := C*U*V + A + B + E*W
  let KN := C*U + 1
  have hKP : 0 < KP := by dsimp [KP]; positivity
  have hKN : 0 < KN := by dsimp [KN]; positivity
  refine ⟨KP+KN, add_pos hKP hKN, ?_⟩
  intro grid w hw n hn t ht1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : 0 ≤ t^(-((1+eta)/beta)) := (Real.rpow_pos_of_pos ht _).le
  have hsmall : t^(-(eta/beta)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht1 (neg_nonpos.mpr (div_pos he hb).le)
  have hprod : t^(-(eta/beta))*t^(-(1/beta)) = t^(-((1+eta)/beta)) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hscaled : (1/(c*t/4))^(1/beta)*Real.Gamma (1+1/beta) =
      V*t^(-(1/beta)) := by
    have hh : c*t/4 = (c/4)*t := by ring
    rw [hh, reciprocal_scaled_rpow (by positivity) ht]
    dsimp [V]
    ring
  have hnear : C*t*(1/(c*t/4))^((beta+eta)/beta)*
      ((1/(c*t/4))^(1/beta)*Real.Gamma (1+1/beta)+1/(n : ℝ)) ≤
      C*U*V*t^(-((1+eta)/beta)) + (C*U)/(n : ℝ) := by
    have hi := right_perturbation_power_identity hc hb ht (eta := eta)
    change t*(1/(c*t/4))^((beta+eta)/beta) = U*t^(-(eta/beta)) at hi
    rw [show C*t*(1/(c*t/4))^((beta+eta)/beta) = C*(U*t^(-(eta/beta))) by
      rw [mul_assoc C t, hi], hscaled]
    calc
      _ = C*U*V*(t^(-(eta/beta))*t^(-(1/beta))) +
          (C*U)/(n : ℝ)*t^(-(eta/beta)) := by ring
      _ ≤ _ := by
        rw [hprod]
        exact add_le_add_right (by simpa using
          mul_le_mul_of_nonneg_left hsmall (div_nonneg (mul_pos hC hU).le hn0.le)) _
  have htail : Real.exp (-(c*t)/2)*
      ((1/((c*t)/2))^(1/beta)*Real.Gamma (1+1/beta)) ≤
      E*W*t^(-((1+eta)/beta)) := by
    have hh : c*t/2 = (c/2)*t := by ring
    have hhneg : -(c*t)/2 = -((c/2)*t) := by ring
    rw [hhneg, hh, reciprocal_scaled_rpow (half_pos hc) ht]
    calc
      _ ≤ (E*t^(-(eta/beta)))*
          ((c/2)^(-(1/beta))*t^(-(1/beta))*Real.Gamma (1+1/beta)) :=
        mul_le_mul_of_nonneg_right (hEb t ht) (by positivity)
      _ = E*W*(t^(-(eta/beta))*t^(-(1/beta))) := by dsimp [W]; ring
      _ = _ := by rw [hprod]
  have hsum := add_le_add
    (add_le_add (add_le_add (add_le_add hnear (hAb t ht)) (hBb t ht)) (le_refl (1/(n : ℝ))))
    htail
  have hbound := (herr grid w hw n hn t ht).trans (by
    simpa only [survivalKernel, neg_mul, mul_comm t] using hsum)
  calc
    _ ≤ KP*t^(-((1+eta)/beta)) + KN/(n : ℝ) := by
      exact hbound.trans_eq (by dsimp only [KP, KN]; ring)
    _ ≤ (KP+KN)*(t^(-((1+eta)/beta)) + 1/(n : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hKN.le : KP ≤ KP+KN) hp
      have h2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hKP.le : KN ≤ KP+KN)
        (one_div_nonneg.mpr hn0.le)
      calc
        _ = KP*t^(-((1+eta)/beta)) + KN*(1/(n : ℝ)) := by ring
        _ ≤ _ := (add_le_add h1 h2).trans_eq (by ring)

end Luce.Section6
