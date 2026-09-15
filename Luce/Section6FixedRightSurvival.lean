import Luce.Section6RightComparisonDepth
import Luce.Section6ExtremeScale
import Luce.Section6SublinearCutoff
import Luce.Section6TerminalGapSurvival

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Fixed terminal targets, including the infinite final gap, have
stretched-exponential moments for every sufficiently deep source.
No source-corner restriction is required. -/
theorem PowerProfile.fixed_right_kernel_moment {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r H0 : ℕ) :
    ∃ d A N : ℝ, 0 < d ∧ 0 < A ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, N ≤ (n : ℝ) → ∀ i j : Fin n, A ≤ (terminalDepth i : ℝ) →
      terminalDepth j ≤ H0 →
    ∀ removed : Finset (Fin n), removed.card ≤ r → ∀ k p : ℕ,
      Nat.dist k j.val ≤ r+1 → 1 ≤ p →
      (∫ old, (deletedGapKernel (w n) removed old i k).toReal^p ∂exponentialRace (w n)) ≤
        2*Real.exp (-d*(terminalDepth i : ℝ)^(beta/(beta+1))) := by
  obtain ⟨d, H, delta, hd, hH, hdelta, hdelta1, hb⟩ := hp.right_comparison_depth_survival r
  let L : ℕ := max (8*r+8) (H0+r+1)
  have hL : 0 < (L : ℝ) := Nat.cast_pos.mpr (by dsimp [L]; omega)
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  obtain ⟨A, hA, hcut⟩ := right_extreme_depth_cutoff (lt_max_of_lt_left hH) hbeta
    (H := max H (L : ℝ))
  have hz := right_extreme_exponent_bounds hbeta
  obtain ⟨N, hN, hncut⟩ := sublinear_power_cutoff (H := H) hz.1 hz.2 hdelta
  refine ⟨d, A, N, hd, hA, hN, ?_⟩
  intro grid w hw n hnN i j hi hj removed hremoved k p hshift hpp
  have hn : 0 < n := by have := j.isLt; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let y : ℝ := (terminalDepth i : ℝ)^(beta/(beta+1))
  obtain ⟨ha1, hay⟩ := hcut (terminalDepth i : ℝ) hi
  have hHy : H ≤ y := (le_max_left _ _).trans hay
  have hLy : (L : ℝ) ≤ y := (le_max_right _ _).trans hay
  have hle : y ≤ (terminalDepth i : ℝ) := right_extreme_depth_le ha1 hbeta
  have hain : (terminalDepth i : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n i.val)
  have hLn : L ≤ n := by exact_mod_cast hLy.trans (hle.trans hain)
  have hysmall : y/(n : ℝ) < delta :=
    (div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hain hz.1.le) hnR.le).trans_lt (hncut n hnN).2.2
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hq : n-L < (Finset.univ \ removed).card := by rw [hcard]; dsimp [L] at *; omega
  have hqk : n-L ≤ k := by
    unfold Nat.dist at hshift
    unfold terminalDepth at hj
    dsimp [L]
    have := j.isLt
    omega
  have ht := hb grid w hw n L y hn hHy (by dsimp [L]; omega) hLy hysmall
    removed hremoved i ⟨n-L, hq⟩ p hpp (by simp)
  have hid : ((terminalDepth i : ℝ)/y)^beta = y :=
    right_extreme_scale_identity (Nat.cast_pos.mpr (terminalDepth_pos i)) hbeta
  rw [hid] at ht
  have hm := deleted_gap_moment_le_earlier_survival (w n) removed i ⟨n-L, hq⟩ k p hqk
  exact hm.trans (by simpa only [two_mul] using ht)

end Luce.Section6
