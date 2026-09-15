import Luce.Section6TerminalReference
import Luce.Section6LogarithmicSurvival
import Luce.Section6TwoExponentialBounds

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- A finite logarithmic reference gap controls the actual terminal window,
including its infinite final gap. No endpoint assumption is needed here. -/
theorem terminal_logarithmic_insertion_Lp {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 1))
    (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x)
    (p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r Q h : ℕ, 8 ≤ n → 16*r ≤ n → 8*r+Q+8 ≤ h → 16384*h ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (k p : ℕ), (Finset.univ \ removed).card ≤ k+Q →
    1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i k).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*(Real.exp (-d*((w n).rate i*Real.log ((n : ℝ)/(h : ℝ))))+
        Real.exp (-d*Real.sqrt ((n : ℝ)*(h : ℝ))))) := by
  obtain ⟨d, hd, hs⟩ := logarithmic_survival_envelope hf hpos
  have hp0R : (0 : ℝ) < p0 := Nat.cast_pos.mpr hp0
  refine ⟨2*(p0.factorial : ℝ), d/(p0 : ℝ), by positivity, div_pos hd hp0R, ?_⟩
  intro grid w hw n r Q h hn hr hh hsmall removed hremoved i k p hk hpp hpp0
  obtain ⟨q, hq, hqk⟩ := terminal_window_reference_gap (h := h) removed (by omega) (by omega) hk
  have hshift : Nat.dist q.val (n-h) ≤ r+1 := by rw [hq]; simp
  have hs0 := hs grid w hw n r h hn hr (by omega) hsmall removed hremoved i q p hpp hshift
  have hm := (deleted_gap_moment_le_earlier_survival (w n) removed i q k p hqk).trans hs0
  let x := (w n).rate i*Real.log ((n : ℝ)/(h : ℝ))
  let y := Real.sqrt ((n : ℝ)*(h : ℝ))
  have hi := (w n).positive i
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast (show h ≤ n by omega)
  have hx : 0 ≤ x := mul_nonneg hi.le (Real.log_nonneg ((one_le_div hhR).mpr hhnR))
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hm0 := hm.trans (sum_exp_neg_le_twice_min hd.le)
  have hfact : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.factorial_pos p
  have hm1 : (∫ old, (deletedGapKernel (w n) removed old i k).toReal^p ∂exponentialRace (w n)) ≤
      2*(p.factorial : ℝ)*(1*1)^p*Real.exp (-d*min x y) := by
    simp only [mul_one, one_pow]
    nlinarith [Real.exp_pos (-d*min x y)]
  have hpw := hm1.trans (uniform_moment_decay hpp hpp0 (B := 1) (z := 1)
    zero_le_one zero_le_one hd.le (le_min hx hy))
  have he := deleted_kernel_eLpNorm_le_of_moment (w n) removed i k p (by omega) (by positivity) hpw
  simp only [mul_one] at he
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (exp_neg_min_le_sum (d/(p0 : ℝ)) x y) (by positivity)

end Luce.Section6
