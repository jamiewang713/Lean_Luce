import Luce.Section6FastPopulationComparison
import Luce.Section6FastArrivalPrototype

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem PowerProfile.left_populationG_power_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) :
    ∃ eta' : ℝ, 0 < eta' ∧ eta' < eta ∧ eta' < alpha-1 ∧
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → t ≤ 1 →
    |populationG (w n) t - Real.Gamma (1-1/alpha)*c^(1/alpha)*t^(1/alpha)| ≤
      K*(t^(1/(alpha-eta'))+1/(n : ℝ)) := by
  have hc := h.2.2.1.1
  have ha := h.2.2.1.2.1
  obtain ⟨eta', he, heeta, healpha, C, hC, hcomp⟩ := h.left_populationG_comparison
  have hq : 1 < alpha-eta' := by linarith
  have hq0 : 0 < alpha-eta' := zero_lt_one.trans hq
  let B := c/(alpha-1)
  have hB : 0 < B := div_pos hc (sub_pos.mpr ha)
  refine ⟨eta', he, heeta, healpha, C+1+B, by positivity, ?_⟩
  intro grid w hw n hn t ht ht1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsmall : t ≤ t^(1/(alpha-eta')) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1
      ((div_le_one hq0).mpr hq.le)
  have hp := fast_arrival_prototype_error grid hn ha (mul_pos hc ht)
  have hlead : (c*t)^(1/alpha)*Real.Gamma (1-1/alpha) =
      Real.Gamma (1-1/alpha)*c^(1/alpha)*t^(1/alpha) := by
    rw [Real.mul_rpow hc.le ht.le]
    ring
  rw [hlead] at hp
  calc
    _ ≤ |populationG (w n) t -
        (∑ i : Fin n, (1-Real.exp (-((c*t)*(samplePoint grid n i)^(-alpha)))))/(n : ℝ)| +
        |(∑ i : Fin n, (1-Real.exp (-((c*t)*(samplePoint grid n i)^(-alpha)))))/(n : ℝ) -
        Real.Gamma (1-1/alpha)*c^(1/alpha)*t^(1/alpha)| := abs_sub_le _ _ _
    _ ≤ C*(t^(1/(alpha-eta'))+1/(n : ℝ)) + (1/(n : ℝ)+(c*t)/(alpha-1)) :=
      add_le_add (hcomp grid w hw n hn t ht ht1) hp
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hsmall hB.le
      have h1 := (Real.rpow_pos_of_pos ht (1/(alpha-eta'))).le
      have h2 := mul_nonneg hB.le (one_div_nonneg.mpr hn0.le)
      have hid : (c*t)/(alpha-1) = B*t := by dsimp [B]; ring
      rw [hid]
      nlinarith

/-- The left-arrival part of the manuscript's population lemma. The error
exponent is constructed from the permitted expansion; it is not an input. -/
theorem PowerProfile.left_populationG_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) :
    ∃ zeta K : ℝ, 0 < zeta ∧ 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → t ≤ 1 →
    |populationG (w n) t /
        (Real.Gamma (1-1/alpha)*c^(1/alpha)*t^(1/alpha)) - 1| ≤
      K*(t^zeta+1/((n : ℝ)*t^(1/alpha))) := by
  have hc := h.2.2.1.1
  have ha := h.2.2.1.2.1
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  have hg : 0 < 1-1/alpha := by
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  let A := Real.Gamma (1-1/alpha)*c^(1/alpha)
  have hA : 0 < A := mul_pos (Real.Gamma_pos_of_pos hg) (Real.rpow_pos_of_pos hc _)
  obtain ⟨eta', he, _, healpha, C, hC, hbound⟩ := h.left_populationG_power_error
  have hq0 : 0 < alpha-eta' := by linarith
  let zeta := 1/(alpha-eta')-1/alpha
  have hz : 0 < zeta := sub_pos.mpr (one_div_lt_one_div_of_lt hq0 (by linarith))
  refine ⟨zeta, C/A, hz, div_pos hC hA, ?_⟩
  intro grid w hw n hn t ht ht1
  have hp : 0 < t^(1/alpha) := Real.rpow_pos_of_pos ht _
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have herr := hbound grid w hw n hn t ht ht1
  change |populationG (w n) t - A*t^(1/alpha)| ≤ _ at herr
  have hprod : t^zeta*t^(1/alpha) = t^(1/(alpha-eta')) := by
    rw [← Real.rpow_add ht]
    congr 1
    dsimp [zeta]
    ring
  change |populationG (w n) t / (A*t^(1/alpha)) - 1| ≤ _
  rw [div_sub_one (mul_pos hA hp).ne', abs_div, abs_of_pos (mul_pos hA hp)]
  apply (div_le_iff₀ (mul_pos hA hp)).mpr
  calc
    _ ≤ C*(t^(1/(alpha-eta'))+1/(n : ℝ)) := herr
    _ = _ := by rw [← hprod]; field_simp

end Luce.Section6
