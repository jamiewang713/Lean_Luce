import Luce.Section6WeightedPopulationRegions
import Luce.Section6PowerWindowRegions

noncomputable section
namespace Luce.Section6

/-- Both-grid power bounds throughout the enlarged left quantile window,
with every evaluation-region condition derived from the original inputs. -/
theorem PowerProfile.left_populationD_quantile_window {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ delta M : ℝ, 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := leftQuantileTime (w n) m
      ∀ s : ℝ, t/8 ≤ s → s ≤ 8*t →
        let B := (Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*s^(1/alpha-1)
        B/2 ≤ populationD (w n) 1 s ∧ populationD (w n) 1 s ≤ 2*B := by
  have hc := hp.2.2.1.1
  have ha := hp.2.2.1.2.1
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  have hG : 0 < Real.Gamma (1-1/alpha) := by
    apply Real.Gamma_pos_of_pos
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  let A := Real.Gamma (1-1/alpha)*c^(1/alpha)
  have hA : 0 < A := mul_pos hG (Real.rpow_pos_of_pos hc _)
  obtain ⟨S, L, hS, _, hL, hpopulation⟩ := hp.left_populationD_comparable
  obtain ⟨dr, Mr, hdr, hMr, hregion⟩ := positive_power_window_region hA
    (one_div_pos.mpr ha0) hS hL
  obtain ⟨dt, Mt, hdt, hMt, htime⟩ := hp.left_quantile_comparable
  refine ⟨min dr dt, max Mr Mt, lt_min hdr hdt, hMr.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  have hn : 0 < n := hm.trans hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let T := ((m : ℝ)/(A*(n : ℝ)))^alpha
  let t := leftQuantileTime (w n) m
  have ht := htime grid w hw n m hm hmn ((le_max_right _ _).trans hlarge)
    (hsmall.trans_le (min_le_right _ _))
  change T/2 ≤ t ∧ t ≤ 2*T at ht
  have hr := hregion (n : ℝ) (m : ℝ) hnR hmR ((le_max_left _ _).trans hlarge)
    (hsmall.trans_le (min_le_left _ _))
  have hInv : (1 : ℝ)/(1/alpha) = alpha := by field_simp
  have hScale : ((m : ℝ)/(n : ℝ))/A = (m : ℝ)/(A*(n : ℝ)) := by field_simp
  simp only [hInv, hScale] at hr
  change ∀ s : ℝ, t/8 ≤ s → s ≤ 8*t →
    (A/alpha*s^(1/alpha-1))/2 ≤ populationD (w n) 1 s ∧
      populationD (w n) 1 s ≤ 2*(A/alpha*s^(1/alpha-1))
  intro s hslo hshi
  have hr' := hr s (by change T/16 ≤ s; linarith [ht.1]) (by change s ≤ 16*T; linarith [ht.2])
  have ht0 := (leftQuantileTime_spec (w n) hm hmn).1
  have hs0 : 0 < s := by change 0 < t at ht0; linarith
  exact hpopulation grid w hw n hn s hs0 hr'.1 hr'.2

end Luce.Section6
