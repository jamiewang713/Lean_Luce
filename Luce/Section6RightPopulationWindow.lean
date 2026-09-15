import Luce.Section6WeightedPopulationRegions
import Luce.Section6PowerWindowRegions

noncomputable section
namespace Luce.Section6

/-- The entire enlarged time window about the right quantile satisfies
the weighted-population power bounds. The enlargement also covers s/2
when applying the second-moment inequality. -/
theorem PowerProfile.right_populationD_quantile_window {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ delta M : ℝ, 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := rightQuantileTime (w n) m
      ∀ s : ℝ, t/8 ≤ s → s ≤ 8*t →
        let B := (Real.Gamma (1+1/beta)*c^(-(1/beta))/beta)*s^(-1-1/beta)
        B/2 ≤ populationD (w n) 1 s ∧ populationD (w n) 1 s ≤ 2*B := by
  have hc := hp.2.2.2.1.1
  have hb := hp.2.2.2.1.2.1
  let A := Real.Gamma (1+1/beta)*c^(-(1/beta))
  have hA : 0 < A := mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hc _)
  obtain ⟨S, L, hS, hL, hpopulation⟩ := hp.right_populationD_comparable
  obtain ⟨dr, Mr, hdr, hMr, hregion⟩ := negative_power_window_region hA
    (one_div_pos.mpr hb) (zero_lt_one.trans_le hS) hL
  obtain ⟨dt, Mt, hdt, hMt, htime⟩ := hp.right_quantile_comparable
  refine ⟨min dr dt, max Mr Mt, lt_min hdr hdt, hMr.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  have hn : 0 < n := hm.trans hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let T := (A*(n : ℝ)/(m : ℝ))^beta
  let t := rightQuantileTime (w n) m
  have ht := htime grid w hw n m hm hmn ((le_max_right _ _).trans hlarge)
    (hsmall.trans_le (min_le_right _ _))
  change T/2 ≤ t ∧ t ≤ 2*T at ht
  have hr := hregion (n : ℝ) (m : ℝ) hnR hmR ((le_max_left _ _).trans hlarge)
    (hsmall.trans_le (min_le_left _ _))
  have hInv : (1 : ℝ)/(1/beta) = beta := by field_simp
  have hScale : A/((m : ℝ)/(n : ℝ)) = A*(n : ℝ)/(m : ℝ) := by field_simp
  simp only [hInv, hScale] at hr
  change ∀ s : ℝ, t/8 ≤ s → s ≤ 8*t →
    (A/beta*s^(-1-1/beta))/2 ≤ populationD (w n) 1 s ∧
      populationD (w n) 1 s ≤ 2*(A/beta*s^(-1-1/beta))
  intro s hslo hshi
  have hr' := hr s (by change T/16 ≤ s; linarith [ht.1]) (by change s ≤ 16*T; linarith [ht.2])
  exact hpopulation grid w hw n hn s hr'.1 hr'.2

end Luce.Section6
