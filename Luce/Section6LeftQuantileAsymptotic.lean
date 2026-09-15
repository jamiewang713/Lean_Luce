import Luce.Section6MonotoneQuantileError
import Luce.Section6FiniteQuantiles
import Luce.Section6LeftArrivalAsymptotic

noncomputable section
namespace Luce.Section6

/-- The left deterministic time in `eq:sp-left-quantile`. The positive
error exponent and all constants are constructed from the original
profile, uniformly over both grids and all ranks in the joint regime. -/
theorem PowerProfile.left_quantile_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ xi C delta M : ℝ, 0 < xi ∧ 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      |leftQuantileTime (w n) m /
        ((m : ℝ)/((Real.Gamma (1-1/alpha)*c^(1/alpha))*(n : ℝ)))^alpha-1| ≤
      C*(((m : ℝ)/(n : ℝ))^xi+1/(m : ℝ)) := by
  have hc := hp.2.2.1.1
  have ha := hp.2.2.1.2.1
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  have hg : 0 < 1-1/alpha := by
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  let A := Real.Gamma (1-1/alpha)*c^(1/alpha)
  have hA : 0 < A := mul_pos (Real.Gamma_pos_of_pos hg) (Real.rpow_pos_of_pos hc _)
  obtain ⟨eta', he, _, healpha, K, hK, hpopulation⟩ := hp.left_populationG_power_error
  have hden : 0 < alpha-eta' := by linarith
  let q := 1/(alpha-eta')-1/alpha
  have hq : 0 < q := sub_pos.mpr (one_div_lt_one_div_of_lt hden (by linarith))
  have hp0 : 0 < 1/alpha := one_div_pos.mpr ha0
  obtain ⟨C, delta, M, hC, hd, hM, hinv⟩ :=
    monotone_positive_power_quantile_error hA hp0 hq hK
  refine ⟨q/(1/alpha), C, delta, M, div_pos hq hp0, hC, hd, hM, ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  have hn : 0 < n := hm.trans hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hbound (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
      |populationG (w n) s-A*s^(1/alpha)| ≤
        K*(s^(1/alpha+q)+1/(n : ℝ)) := by
    have hh := hpopulation grid w hw n hn s hs hs1
    have hExp : 1/alpha+q = 1/(alpha-eta') := by dsimp [q]; ring
    simpa only [hExp] using hh
  have hspec := leftQuantileTime_spec (w n) hm hmn
  have hNx : (n : ℝ)*((m : ℝ)/(n : ℝ)) = (m : ℝ) := by field_simp
  have hh := hinv (n : ℝ) hnR (populationG (w n))
    (populationG_strictMono hn (w n)).monotone hbound
    ((m : ℝ)/(n : ℝ)) (leftQuantileTime (w n) m) (div_pos hmR hnR) hsmall
    (by simpa only [hNx] using hlarge) hspec.1 hspec.2
  have hInv : (1 : ℝ)/(1/alpha) = alpha := by field_simp
  have hScale : ((m : ℝ)/(n : ℝ))/A = (m : ℝ)/(A*(n : ℝ)) := by field_simp
  simpa only [hNx, hInv, hScale] using hh

end Luce.Section6
