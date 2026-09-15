import Luce.Section6AntitoneQuantileError
import Luce.Section6FiniteQuantiles
import Luce.Section6RightSurvivorRelative

noncomputable section
namespace Luce.Section6

/-- The right deterministic quantile in `eq:sp-right-quantile`, with the
exact Gamma leading coefficient and a quantitative error uniform in the
joint regime m large and m/n small, on both sampling grids. -/
theorem PowerProfile.right_quantile_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ C delta M : ℝ, 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      |rightQuantileTime (w n) m /
        ((Real.Gamma (1+1/beta)*c^(-(1/beta)))*(n : ℝ)/(m : ℝ))^beta-1| ≤
      C*(((m : ℝ)/(n : ℝ))^eta+1/(m : ℝ)) := by
  have hc := hp.2.2.2.1.1
  have hb := hp.2.2.2.1.2.1
  have he := hp.2.2.2.1.2.2.1
  let A := Real.Gamma (1+1/beta)*c^(-(1/beta))
  have hA : 0 < A := mul_pos (Real.Gamma_pos_of_pos (by positivity))
    (Real.rpow_pos_of_pos hc _)
  obtain ⟨K, hK, hpopulation⟩ := hp.right_populationH_power_error
  obtain ⟨C, delta, M, hC, hd, hM, hinv⟩ :=
    antitone_negative_power_quantile_error hA (one_div_pos.mpr hb) (div_pos he hb) hK
  refine ⟨C, delta, M, hC, hd, hM, ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  have hn : 0 < n := hm.trans hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hbound (s : ℝ) (hs : 1 ≤ s) :
      |populationH (w n) s-A*s^(-(1/beta))| ≤
        K*(s^(-(1/beta+eta/beta))+1/(n : ℝ)) := by
    have hs0 : 0 < s := zero_lt_one.trans_le hs
    have hh := hpopulation grid w hw n hn s hs
    have hlead : (1/(c*s))^(1/beta)*Real.Gamma (1+1/beta) = A*s^(-(1/beta)) := by
      rw [reciprocal_scaled_rpow hc hs0]
      dsimp [A]
      ring
    rw [hlead, show (1+eta)/beta = 1/beta+eta/beta by ring] at hh
    exact hh
  have hspec := rightQuantileTime_spec (w n) hm hmn
  have hNx : (n : ℝ)*((m : ℝ)/(n : ℝ)) = (m : ℝ) := by field_simp
  have hh := hinv (n : ℝ) hnR (populationH (w n))
    (populationH_strictAnti hn (w n)).antitone hbound
    ((m : ℝ)/(n : ℝ)) (rightQuantileTime (w n) m) (div_pos hmR hnR) hsmall
    (by simpa only [hNx] using hlarge) hspec.1 hspec.2
  have hInv : (1 : ℝ)/(1/beta) = beta := by field_simp
  have hExp : (eta/beta)/(1/beta) = eta := by field_simp
  have hScale : A/((m : ℝ)/(n : ℝ)) = A*(n : ℝ)/(m : ℝ) := by field_simp
  simpa only [hNx, hInv, hExp, hScale] using hh

end Luce.Section6
