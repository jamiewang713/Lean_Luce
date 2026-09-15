import Luce.Section6AntitoneQuantileControl
import Luce.Section6NegativePowerComparison
import Luce.Section6RightWeightedAsymptotic
import Luce.Section6RightQuantileAsymptotic

noncomputable section
namespace Luce.Section6

/-- The weighted population at the exact survivor quantile. Every
smallness premise is discharged from the original profile and sampling. -/
theorem PowerProfile.right_quantile_scaledD_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ C delta M : ℝ, 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := rightQuantileTime (w n) m
      |beta*t*populationD (w n) 1 t/((m : ℝ)/(n : ℝ))-1| ≤
        C*(((m : ℝ)/(n : ℝ))^eta+1/(m : ℝ)) := by
  have hc := hp.2.2.2.1.1
  have hb := hp.2.2.2.1.2.1
  have he := hp.2.2.2.1.2.2.1
  let A := Real.Gamma (1+1/beta)*c^(-(1/beta))
  let B := A/beta
  have hA : 0 < A := mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hc _)
  have hB : 0 < B := div_pos hA hb
  obtain ⟨K, hK, hsurv⟩ := hp.right_populationH_power_error
  obtain ⟨L, hL, hweighted⟩ := hp.right_scaled_populationD_power_error
  obtain ⟨delta, M, hd, hM, hcontrol⟩ :=
    antitone_quantile_smallness hA (one_div_pos.mpr hb) (div_pos he hb) hK
  obtain ⟨C, hC, hcompare⟩ :=
    negative_power_weighted_comparison hA hB (one_div_pos.mpr hb) (div_pos he hb) hK hL
  refine ⟨C, delta, M, hC, hd, hM, ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  have hn : 0 < n := hm.trans hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let x := (m : ℝ)/(n : ℝ)
  let t := rightQuantileTime (w n) m
  have hx : 0 < x := div_pos hmR hnR
  have hExp : (1+eta)/beta = 1/beta+eta/beta := by ring
  have hH (s : ℝ) (hs : 1 ≤ s) : |populationH (w n) s-A*s^(-(1/beta))| ≤
      K*(s^(-(1/beta+eta/beta))+1/(n : ℝ)) := by
    have hh := hsurv grid w hw n hn s hs
    have hlead : (1/(c*s))^(1/beta)*Real.Gamma (1+1/beta) = A*s^(-(1/beta)) := by
      rw [reciprocal_scaled_rpow hc (zero_lt_one.trans_le hs)]
      dsimp [A]
      ring
    simpa only [hlead, hExp] using hh
  have hD (s : ℝ) (hs : 1 ≤ s) : |s*populationD (w n) 1 s-B*s^(-(1/beta))| ≤
      L*(s^(-(1/beta+eta/beta))+1/(n : ℝ)) := by
    have hh := hweighted grid w hw n hn s hs
    have hlead : (Real.Gamma (1+1/beta)/beta)*c^(-(1/beta)) = B := by dsimp [B, A]; ring
    simpa only [hlead, hExp] using hh
  have hspec := rightQuantileTime_spec (w n) hm hmn
  have hNx : (n : ℝ)*x = (m : ℝ) := by dsimp [x]; field_simp
  obtain ⟨ht1, htSmall, hdisc⟩ := hcontrol (n : ℝ) hnR (populationH (w n))
    (populationH_strictAnti hn (w n)).antitone hH x t hx hsmall
    (by simpa only [hNx] using hlarge) hspec.1 hspec.2
  have hHt : |x-A*t^(-(1/beta))| ≤ K*(t^(-(1/beta+eta/beta))+1/(n : ℝ)) := by
    have hxeq : populationH (w n) t = x := hspec.2
    rw [← hxeq]
    exact hH t ht1
  have hh := hcompare (n : ℝ) x t (t*populationD (w n) 1 t) hnR hx hspec.1
    hHt (hD t ht1) htSmall hdisc
  have hpow : (eta/beta)/(1/beta) = eta := by field_simp
  have hid : (t*populationD (w n) 1 t)/(B*x/A) = beta*t*populationD (w n) 1 t/x := by
    dsimp [B]
    field_simp
  simpa only [hid, hpow, hNx] using hh

end Luce.Section6
