import Luce.Section6RightPopulationAsymptotic

noncomputable section
namespace Luce.Section6

/-- The right-survivor assertion of `lem:sp-populations`, with the exact
Gamma coefficient and a concrete positive saving eta/beta. Constants are
uniform in the grid and the sampled array. -/
theorem PowerProfile.right_populationH_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 1 ≤ t →
    |populationH (w n) t /
        (Real.Gamma (1+1/beta)*c^(-(1/beta))*t^(-(1/beta))) - 1| ≤
      K*(t^(-(eta/beta)) + 1/((n : ℝ)*t^(-(1/beta)))) := by
  have hc : 0 < c := h.2.2.2.1.1
  have hb : 0 < beta := h.2.2.2.1.2.1
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  let A := Real.Gamma (1+1/beta)*c^(-(1/beta))
  have hA : 0 < A := mul_pos hG (Real.rpow_pos_of_pos hc _)
  obtain ⟨K, hK, hbound⟩ := h.right_populationH_power_error
  refine ⟨K/A, div_pos hK hA, ?_⟩
  intro grid w hw n hn t ht1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hp : 0 < t^(-(1/beta)) := Real.rpow_pos_of_pos ht _
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlead : (1/(c*t))^(1/beta)*Real.Gamma (1+1/beta) =
      A*t^(-(1/beta)) := by
    rw [reciprocal_scaled_rpow hc ht]
    dsimp [A]
    ring
  have herr := hbound grid w hw n hn t ht1
  rw [hlead] at herr
  have hprod : t^(-(eta/beta))*t^(-(1/beta)) = t^(-((1+eta)/beta)) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  change |populationH (w n) t / (A*t^(-(1/beta))) - 1| ≤ _
  rw [div_sub_one (mul_pos hA hp).ne', abs_div, abs_of_pos (mul_pos hA hp)]
  apply (div_le_iff₀ (mul_pos hA hp)).mpr
  calc
    _ ≤ K*(t^(-((1+eta)/beta)) + 1/(n : ℝ)) := herr
    _ = _ := by
      rw [← hprod]
      field_simp

end Luce.Section6
