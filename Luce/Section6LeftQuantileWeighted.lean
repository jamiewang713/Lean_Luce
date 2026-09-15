import Luce.Section6MonotoneQuantileControl
import Luce.Section6PositivePowerComparison
import Luce.Section6LeftCommonPopulationError
import Luce.Section6FiniteQuantiles

noncomputable section
namespace Luce.Section6

/-- The weighted population at the exact arrival quantile, with a
positive error exponent constructed from the original profile. -/
theorem PowerProfile.left_quantile_scaledD_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ xi C delta M : ℝ, 0 < xi ∧ 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := leftQuantileTime (w n) m
      |alpha*t*populationD (w n) 1 t/((m : ℝ)/(n : ℝ))-1| ≤
        C*(((m : ℝ)/(n : ℝ))^xi+1/(m : ℝ)) := by
  have hc := hp.2.2.1.1
  have ha := hp.2.2.1.2.1
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  have hG : 0 < Real.Gamma (1-1/alpha) := by
    apply Real.Gamma_pos_of_pos
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  let A := Real.Gamma (1-1/alpha)*c^(1/alpha)
  let B := A/alpha
  have hA : 0 < A := mul_pos hG (Real.rpow_pos_of_pos hc _)
  have hB : 0 < B := div_pos hA ha0
  have hp0 : 0 < 1/alpha := one_div_pos.mpr ha0
  obtain ⟨q, K, hq, hK, hpopulation⟩ := hp.left_populations_power_error
  obtain ⟨delta, M, hd, hM, hcontrol⟩ := monotone_quantile_smallness hA hp0 hq hK
  obtain ⟨C, hC, hcompare⟩ := positive_power_weighted_comparison hA hB hp0 hq hK hK
  refine ⟨q/(1/alpha), C, delta, M, div_pos hq hp0, hC, hd, hM, ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  have hn : 0 < n := hm.trans hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let x := (m : ℝ)/(n : ℝ)
  let t := leftQuantileTime (w n) m
  have hx : 0 < x := div_pos hmR hnR
  have hGb (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
      |populationG (w n) s-A*s^(1/alpha)| ≤ K*(s^(1/alpha+q)+1/(n : ℝ)) :=
    (hpopulation grid w hw n hn s hs hs1).1
  have hDb (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
      |s*populationD (w n) 1 s-B*s^(1/alpha)| ≤ K*(s^(1/alpha+q)+1/(n : ℝ)) :=
    (hpopulation grid w hw n hn s hs hs1).2
  have hspec := leftQuantileTime_spec (w n) hm hmn
  have hNx : (n : ℝ)*x = (m : ℝ) := by dsimp [x]; field_simp
  obtain ⟨ht1, htSmall, hdisc⟩ := hcontrol (n : ℝ) hnR (populationG (w n))
    (populationG_strictMono hn (w n)).monotone hGb x t hx hsmall
    (by simpa only [hNx] using hlarge) hspec.1 hspec.2
  have hGt : |x-A*t^(1/alpha)| ≤ K*(t^(1/alpha+q)+1/(n : ℝ)) := by
    have hxeq : populationG (w n) t = x := hspec.2
    rw [← hxeq]
    exact hGb t hspec.1 ht1
  have hh := hcompare (n : ℝ) x t (t*populationD (w n) 1 t) hnR hx hspec.1
    hGt (hDb t hspec.1 ht1) htSmall hdisc
  have hid : (t*populationD (w n) 1 t)/(B*x/A) = alpha*t*populationD (w n) 1 t/x := by
    dsimp [B]
    field_simp
  simpa only [hid, hNx] using hh

end Luce.Section6
