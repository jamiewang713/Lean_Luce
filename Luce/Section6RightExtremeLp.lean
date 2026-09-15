import Luce.Section6ExtremeRatios
import Luce.Section6ExtremeMomentAbsorption
import Luce.Section6RightExtremeSurvival

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Right extreme insertion Lp bound, uniformly over the prescribed finite
moment range. No moment, tail, or polynomial comparison is assumed. -/
theorem PowerProfile.right_extreme_insertion_Lp {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p0 : ℕ) (hp0 : 0 < p0)
    (v : ℝ) (hv : 0 < v) :
    ∃ C d nu H delta : ℝ, 0 < C ∧ 0 < d ∧ 0 < nu ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ i : Fin n, (terminalDepth i : ℝ)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
    Nat.dist q.val (n-h) ≤ r+1 →
    ¬ ((terminalDepth i : ℝ)/(h : ℝ))^beta ≤ (min (terminalDepth i : ℝ) (h : ℝ))^v →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*Real.exp (-d*(terminalDepth i : ℝ)^nu)) := by
  obtain ⟨B, dm, hB, hdm, hdm1, hmoment⟩ := hp.right_shifted_insertion_moment
  obtain ⟨ds, Hs, dls, hds, hHs, hdls, hdls1, hsurv⟩ := hp.right_extreme_survival r
  have hb : 0 < beta := hp.2.2.2.1.2.1
  let k := beta*v/(beta+v)
  let zeta := beta/(beta+1)
  let nu := min k zeta / 2
  have hk : 0 < k := div_pos (mul_pos hb hv) (add_pos hb hv)
  have hzeta : 0 < zeta := (right_extreme_exponent_bounds hb).1
  have hnu : 0 < nu := div_pos (lt_min hk hzeta) (by norm_num)
  have hnuk : nu ≤ k := by dsimp [nu]; have := min_le_left k zeta; linarith
  have hnuz : nu ≤ zeta := by dsimp [nu]; have := min_le_right k zeta; linarith
  obtain ⟨C, hC, habs⟩ := extreme_moment_absorption hB hds hb.le hnu p0 hp0
  refine ⟨C, ds/(2*(p0 : ℝ)), nu, max 1 Hs, min dm dls, hC, by positivity,
    hnu, zero_lt_one.trans_le (le_max_left _ _), lt_min hdm hdls,
    (min_le_left _ _).trans_lt hdm1, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved i hismall q p hpp hpp0 hshift hext
  have ha : (1 : ℝ) ≤ terminalDepth i := by exact_mod_cast terminalDepth_pos i
  have hh1 : (1 : ℝ) ≤ h := (le_max_left _ _).trans hhH
  have ha0 : (0 : ℝ) < terminalDepth i := zero_lt_one.trans_le ha
  have hrat := extreme_ratio_bounds ha hh1 hb hv hext
  have hiH : max 1 Hs ≤ (terminalDepth i : ℝ) := hhH.trans hrat.1.le
  have hx : (terminalDepth i : ℝ)^nu ≤ ((terminalDepth i : ℝ)/(h : ℝ))^beta :=
    (Real.rpow_le_rpow_of_exponent_le ha hnuk).trans hrat.2.2.le
  have hy : (terminalDepth i : ℝ)^nu ≤ (terminalDepth i : ℝ)^zeta :=
    Real.rpow_le_rpow_of_exponent_le ha hnuz
  have hz := ratio_power_over_depth_le ha0.le hh1 hh1 hb.le
  have hm := hmoment grid w hw n r hn removed hremoved i q h p hh
    (hsmall.trans_le (min_le_left _ _)) (hismall.trans_le (min_le_left _ _)) hshift
  have hs := hsurv grid w hw n h hn ((le_max_right _ _).trans hhH) hh
    (hsmall.trans_le (min_le_right _ _)) removed hremoved i ((le_max_right _ _).trans hiH)
    (hismall.trans_le (min_le_right _ _)) q p hpp hshift
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  apply deleted_kernel_eLpNorm_le_of_moment (w n) removed i q.val p (by omega) (by positivity)
  apply habs p hpp hpp0 (terminalDepth i : ℝ) _ _ _ _ ha (by positivity) hz hx hy
  nlinarith only [hm']

end Luce.Section6
