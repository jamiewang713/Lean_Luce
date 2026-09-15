import Luce.Section6PopulationPowerBounds

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- A common scaled perturbation estimate for both survivor and weighted
populations. The grid sum bound is derived, not assumed. -/
theorem scaled_power_envelope_average_bound {beta eta d : ℝ}
    (hb : 0 < beta) (he : 0 < eta) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (grid : SamplingGrid) (n : ℕ), 0 < n →
    ∀ t : ℝ, 1 ≤ t →
      t*((∑ i : Fin n, (samplePoint grid n i)^(beta+eta)*
        Real.exp (-((d*t)*(samplePoint grid n i)^beta)))/(n : ℝ)) ≤
      K*(t^(-((1+eta)/beta))+1/(n : ℝ)) := by
  obtain ⟨C, hC, hsum⟩ := power_envelope_average_bound hb
    (a := beta+eta) (by positivity)
  let U := (d/2)^(-((beta+eta)/beta))
  let V := (d/2)^(-(1/beta))*Real.Gamma (1+1/beta)
  have hU : 0 < U := Real.rpow_pos_of_pos (half_pos hd) _
  have hV : 0 < V := mul_pos (Real.rpow_pos_of_pos (half_pos hd) _)
    (Real.Gamma_pos_of_pos (by positivity))
  refine ⟨C*U*(V+1), by positivity, ?_⟩
  intro grid n hn t ht1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hu : t*(1/((d*t)/2))^((beta+eta)/beta) = U*t^(-(eta/beta)) := by
    have hh := right_perturbation_power_identity (c := 2*d) (eta := eta) (by positivity) hb ht
    have h1 : 2*d*t/4 = d*t/2 := by ring
    have h2 : 2*d/4 = d/2 := by ring
    simpa only [h1, h2, U] using hh
  have hv : (1/((d*t)/2))^(1/beta)*Real.Gamma (1+1/beta) = V*t^(-(1/beta)) := by
    have hh : d*t/2 = (d/2)*t := by ring
    rw [hh, reciprocal_scaled_rpow (half_pos hd) ht]
    dsimp [V]
    ring
  have hprod : t^(-(eta/beta))*t^(-(1/beta)) = t^(-((1+eta)/beta)) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hsmall := Real.rpow_le_one_of_one_le_of_nonpos ht1
    (neg_nonpos.mpr (div_pos he hb).le)
  calc
    _ ≤ t*(C*(1/((d*t)/2))^((beta+eta)/beta)*
        ((1/((d*t)/2))^(1/beta)*Real.Gamma (1+1/beta)+1/(n : ℝ))) :=
      mul_le_mul_of_nonneg_left (hsum grid n hn (d*t) (mul_pos hd ht)) ht.le
    _ = C*U*V*t^(-((1+eta)/beta)) + (C*U)/(n : ℝ)*t^(-(eta/beta)) := by
      rw [show t*(C*(1/((d*t)/2))^((beta+eta)/beta)*
          ((1/((d*t)/2))^(1/beta)*Real.Gamma (1+1/beta)+1/(n : ℝ))) =
          C*(t*(1/((d*t)/2))^((beta+eta)/beta))*
          ((1/((d*t)/2))^(1/beta)*Real.Gamma (1+1/beta)+1/(n : ℝ)) by ring,
        hu, hv]
      calc
        _ = C*U*V*(t^(-(eta/beta))*t^(-(1/beta))) +
            (C*U)/(n : ℝ)*t^(-(eta/beta)) := by ring
        _ = _ := by rw [hprod]
    _ ≤ C*U*V*t^(-((1+eta)/beta)) + (C*U)/(n : ℝ) :=
      add_le_add_right (by simpa using
        mul_le_mul_of_nonneg_left hsmall (div_nonneg (mul_pos hC hU).le hn0.le)) _
    _ ≤ _ := by
      have h1 := mul_nonneg (mul_pos hC hU).le (Real.rpow_pos_of_pos ht (-((1+eta)/beta))).le
      have h2 := mul_nonneg (mul_pos (mul_pos hC hU) hV).le (one_div_nonneg.mpr hn0.le)
      simp only [div_eq_mul_inv, one_mul] at *
      nlinarith

end Luce.Section6
