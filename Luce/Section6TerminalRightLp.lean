import Luce.Section6TerminalOutsideLp
import Luce.Section6RightComparisonDepth
import Luce.Section6KernelLpOne

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Terminal-window norm decay in source depth, including bounded depths
and the infinite final gap. All reference and survival inputs are derived. -/
theorem PowerProfile.terminal_right_depth_Lp {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r Q p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d N : ℝ, 0 < C ∧ 0 < d ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (k p : ℕ), (Finset.univ \ removed).card ≤ k+Q → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i k).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*Real.exp (-d*(terminalDepth i : ℝ)^(beta/(beta+1)))) := by
  obtain ⟨d, H, delta, hd, hH, hdelta, hdelta1, hs⟩ := hp.right_comparison_depth_survival r
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  have hzz := right_extreme_exponent_bounds hbeta
  let h : ℕ := 8*r+Q+8
  obtain ⟨A, hA, hcutA⟩ := right_extreme_depth_cutoff
    (H := max H ((h : ℝ)+1)) (hH.trans_le (le_max_left _ _)) hbeta
  obtain ⟨N, hN, hcutN⟩ := sublinear_power_cutoff (H := 0) hzz.1 hzz.2 hdelta
  let d' := d/(p0 : ℝ)
  have hd' : 0 < d' := div_pos hd (Nat.cast_pos.mpr hp0)
  let C0 : ℝ := 2*(p0.factorial : ℝ)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  let E := Real.exp (d'*A^(beta/(beta+1)))
  have hE : 0 < E := Real.exp_pos _
  refine ⟨C0+E, d', N, add_pos hC0 hE, hd', hN, ?_⟩
  intro grid w hw n hn hnN removed hremoved i k p hk hpp hpp0
  let a : ℝ := terminalDepth i
  let y := a^(beta/(beta+1))
  have ha : 0 < a := Nat.cast_pos.mpr (terminalDepth_pos i)
  have hy : 0 < y := Real.rpow_pos_of_pos ha _
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have han : a ≤ (n : ℝ) := by dsimp [a, terminalDepth]; exact_mod_cast Nat.sub_le n i.val
  change _ ≤ ENNReal.ofReal ((C0+E)*Real.exp (-d'*y))
  by_cases haA : A ≤ a
  · obtain ⟨ha1, hyH⟩ := hcutA a haA
    have hhy : (h : ℝ)+1 ≤ y := (le_max_right _ _).trans hyH
    have hyn : y ≤ (n : ℝ) := (right_extreme_depth_le ha1 hbeta).trans han
    have hhn : h < n := by exact_mod_cast (show (h : ℝ) < n by linarith)
    obtain ⟨q, hq, hqk⟩ := terminal_window_reference_gap removed (by dsimp [h]; omega) hhn hk
    have hshift : Nat.dist q.val (n-h) ≤ r+1 := by rw [hq]; simp
    have hysmall : y/(n : ℝ) < delta :=
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow ha.le han hzz.1.le) hnR.le).trans_lt
        (hcutN (n : ℝ) hnN).2.2
    have hs0 := hs grid w hw n h y hn ((le_max_left _ _).trans hyH)
      (by dsimp [h]; omega) (by linarith) hysmall removed hremoved i q p hpp hshift
    have hscale : ((terminalDepth i : ℝ)/y)^beta = y := right_extreme_scale_identity ha hbeta
    rw [hscale] at hs0
    have hm : (∫ old, (deletedGapKernel (w n) removed old i k).toReal^p ∂exponentialRace (w n)) ≤
        2*(p.factorial : ℝ)*(1*1)^p*Real.exp (-d*y) := by
      have hh0 := (deleted_gap_moment_le_earlier_survival (w n) removed i q k p hqk).trans hs0
      have hf : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.factorial_pos p
      simp only [mul_one, one_pow]
      nlinarith [Real.exp_pos (-d*y)]
    have hpw := hm.trans (uniform_moment_decay hpp hpp0 (B := 1) (z := 1)
      zero_le_one zero_le_one hd.le hy.le)
    have he := deleted_kernel_eLpNorm_le_of_moment (w n) removed i k p (by omega) (by positivity) hpw
    apply he.trans
    apply ENNReal.ofReal_le_ofReal
    change (C0*1)*1*Real.exp (-d'*y) ≤ (C0+E)*Real.exp (-d'*y)
    nlinarith [mul_pos hE (Real.exp_pos (-d'*y))]
  · have hyA : y ≤ A^(beta/(beta+1)) := Real.rpow_le_rpow ha.le (le_of_not_ge haA) hzz.1.le
    have he : 1 ≤ E*Real.exp (-d'*y) := by
      dsimp [E]
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      nlinarith [mul_le_mul_of_nonneg_left hyA hd'.le]
    apply (deleted_kernel_eLpNorm_le_one (w n) removed i k p).trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_pos hC0 (Real.exp_pos (-d'*y))]

end Luce.Section6
