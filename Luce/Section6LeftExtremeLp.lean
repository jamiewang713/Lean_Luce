import Luce.Section6ExtremeRatios
import Luce.Section6ExtremeMomentAbsorption
import Luce.Section6InsertionExponentialMoment

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Left extreme insertion Lp bound, uniformly over the prescribed finite
moment range. No moment, tail, or polynomial comparison is assumed. -/
theorem PowerProfile.left_extreme_insertion_Lp {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p0 : ℕ) (hp0 : 0 < p0)
    (v : ℝ) (hv : 0 < v) :
    ∃ C d nu H delta : ℝ, 0 < C ∧ 0 < d ∧ 0 < nu ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ i : Fin n, ((i.val : ℝ)+1)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
    Nat.dist q.val (h-1) ≤ r+1 →
    ¬ ((h : ℝ)/((i.val : ℝ)+1))^alpha ≤ (min (h : ℝ) ((i.val : ℝ)+1))^v →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*Real.exp (-d*(h : ℝ)^nu)) := by
  obtain ⟨B, ds, Hs, dls, hB, hds, hHs, hdls, hdls1, hmoment⟩ := hp.left_insertion_exponential_moment r
  have hb : 0 < alpha := lt_trans zero_lt_one hp.2.2.1.2.1
  let k := alpha*v/(alpha+v)
  let zeta : ℝ := 1
  let nu := min k zeta / 2
  have hk : 0 < k := div_pos (mul_pos hb hv) (add_pos hb hv)
  have hzeta : 0 < zeta := zero_lt_one
  have hnu : 0 < nu := div_pos (lt_min hk hzeta) (by norm_num)
  have hnuk : nu ≤ k := by dsimp [nu]; have := min_le_left k zeta; linarith
  have hnuz : nu ≤ zeta := by dsimp [nu]; have := min_le_right k zeta; linarith
  obtain ⟨C, hC, habs⟩ := extreme_moment_absorption hB hds hb.le hnu p0 hp0
  refine ⟨C, ds/(2*(p0 : ℝ)), nu, max 1 Hs, dls, hC, by positivity,
    hnu, zero_lt_one.trans_le (le_max_left _ _), hdls, hdls1, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved i hismall q p hpp hpp0 hshift hext
  have ha : (1 : ℝ) ≤ (i.val : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have hh1 : (1 : ℝ) ≤ h := (le_max_left _ _).trans hhH
  have ha0 : (0 : ℝ) < (i.val : ℝ)+1 := zero_lt_one.trans_le ha
  have hrat := extreme_ratio_bounds hh1 ha hb hv hext
  have hx : (h : ℝ)^nu ≤ ((h : ℝ)/((i.val : ℝ)+1))^alpha :=
    (Real.rpow_le_rpow_of_exponent_le hh1 hnuk).trans hrat.2.2.le
  have hy : (h : ℝ)^nu ≤ (h : ℝ) := by
    simpa only [zeta, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hh1 hnuz
  have hz := ratio_power_over_depth_le (Nat.cast_nonneg h) ha hh1 hb.le
  have hm := hmoment grid w hw n h hn ((le_max_right _ _).trans hhH) hh hsmall
    removed hremoved i hismall q p hpp hshift
  apply deleted_kernel_eLpNorm_le_of_moment (w n) removed i q.val p (by omega) (by positivity)
  apply habs p hpp hpp0 (h : ℝ) _ _ _ _ hh1 (by positivity) hz hx hy
  have hnonneg : 0 ≤ (p.factorial : ℝ)*(B*(((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ)))^p*
      (Real.exp (-ds*((h : ℝ)/((i.val : ℝ)+1))^alpha)+Real.exp (-ds*(h : ℝ))) := by positivity
  nlinarith only [hm, hnonneg]

end Luce.Section6
