import Luce.Section6WeightedPopulationComparison
import Luce.Section6WeightedPrototype

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem PowerProfile.right_scaled_populationD_power_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 1 ≤ t →
    |t*populationD (w n) 1 t -
      (Real.Gamma (1+1/beta)/beta)*c^(-(1/beta))*t^(-(1/beta))| ≤
      K*(t^(-((1+eta)/beta))+1/(n : ℝ)) := by
  obtain ⟨C, hC, hc⟩ := h.right_scaled_populationD_comparison
  obtain ⟨E, hE, he⟩ := scaled_weighted_prototype_power_error
    h.2.2.2.1.2.1 h.2.2.2.1.1 h.2.2.2.1.2.2.1
  refine ⟨C+E, add_pos hC hE, ?_⟩
  intro grid w hw n hn t ht
  calc
    _ ≤ |t*populationD (w n) 1 t -
        t*((∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^beta))/(n : ℝ))| +
        |t*((∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^beta))/(n : ℝ)) -
        (Real.Gamma (1+1/beta)/beta)*c^(-(1/beta))*t^(-(1/beta))| := abs_sub_le _ _ _
    _ ≤ C*(t^(-((1+eta)/beta))+1/(n : ℝ)) +
        E*(t^(-((1+eta)/beta))+1/(n : ℝ)) := add_le_add (hc grid w hw n hn t ht) (he grid n hn t ht)
    _ = _ := by ring

theorem time_mul_weighted_power {t : ℝ} (ht : 0 < t) (beta : ℝ) :
    t*t^(-1-1/beta) = t^(-(1/beta)) := by
  conv_lhs => lhs; rw [← Real.rpow_one t]
  rw [← Real.rpow_add ht]
  congr 1
  ring

/-- The right weighted-population assertion of `lem:sp-populations`.
The exact coefficient A divided by beta and saving eta/beta are retained. -/
theorem PowerProfile.right_populationD_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 1 ≤ t →
    |populationD (w n) 1 t /
        ((Real.Gamma (1+1/beta)*c^(-(1/beta))/beta)*t^(-1-1/beta)) - 1| ≤
      K*(t^(-(eta/beta)) + 1/((n : ℝ)*t^(-(1/beta)))) := by
  have hc : 0 < c := h.2.2.2.1.1
  have hb : 0 < beta := h.2.2.2.1.2.1
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  let B := Real.Gamma (1+1/beta)*c^(-(1/beta))/beta
  have hB : 0 < B := div_pos (mul_pos hG (Real.rpow_pos_of_pos hc _)) hb
  obtain ⟨K, hK, hbound⟩ := h.right_scaled_populationD_power_error
  refine ⟨K/B, div_pos hK hB, ?_⟩
  intro grid w hw n hn t ht1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hp : 0 < t^(-(1/beta)) := Real.rpow_pos_of_pos ht _
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlead : (Real.Gamma (1+1/beta)/beta)*c^(-(1/beta))*t^(-(1/beta)) =
      B*t^(-(1/beta)) := by dsimp [B]; ring
  have herr := hbound grid w hw n hn t ht1
  rw [hlead] at herr
  have hprod : t^(-(eta/beta))*t^(-(1/beta)) = t^(-((1+eta)/beta)) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hratio : populationD (w n) 1 t / (B*t^(-1-1/beta)) =
      (t*populationD (w n) 1 t)/(B*t^(-(1/beta))) := by
    rw [← time_mul_weighted_power ht beta]
    field_simp
  change |populationD (w n) 1 t / (B*t^(-1-1/beta)) - 1| ≤ _
  rw [hratio, div_sub_one (mul_pos hB hp).ne', abs_div, abs_of_pos (mul_pos hB hp)]
  apply (div_le_iff₀ (mul_pos hB hp)).mpr
  calc
    _ ≤ K*(t^(-((1+eta)/beta))+1/(n : ℝ)) := herr
    _ = _ := by rw [← hprod]; field_simp

end Luce.Section6
