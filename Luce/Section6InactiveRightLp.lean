import Luce.Section6InactiveRightMoment
import Luce.Section6LogarithmicSurvival
import Luce.Section6TwoExponentialBounds

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The inactive-right insertion norm, with both the remaining-rate floor
and logarithmic survival estimate derived from the original profile. -/
theorem PowerProfile.inactive_right_insertion_Lp {f : ℝ → ℝ}
    {left : EndpointBehavior} {c : ℝ} (hp : PowerProfile f left (.finite c))
    (p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 8 ≤ n → 16*r ≤ n → 8*r+8 ≤ h → 16384*h ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    Nat.dist q.val (n-h) ≤ r+1 → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*((w n).rate i/(h : ℝ))*
        (Real.exp (-d*((w n).rate i*Real.log ((n : ℝ)/(h : ℝ))))+
          Real.exp (-d*Real.sqrt ((n : ℝ)*(h : ℝ))))) := by
  obtain ⟨B, hB, hmoment⟩ := hp.inactive_right_shifted_moment
  obtain ⟨d, hd, hsurvival⟩ := logarithmic_survival_envelope hp.1 hp.2.1
  have hp0R : (0 : ℝ) < p0 := Nat.cast_pos.mpr hp0
  have hf : (0 : ℝ) < p0.factorial := Nat.cast_pos.mpr (Nat.factorial_pos p0)
  refine ⟨2*(p0.factorial : ℝ)*B, d/(p0 : ℝ), by positivity, div_pos hd hp0R, ?_⟩
  intro grid w hw n r h hn hr hh hsmall removed hremoved i q p hshift hpp hpp0
  have hi := (w n).positive i
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast (show h ≤ n by omega)
  have hl := Real.log_nonneg ((one_le_div hhR).mpr hhnR)
  have hx := mul_nonneg hi.le hl
  have hy := Real.sqrt_nonneg ((n : ℝ)*(h : ℝ))
  have hm := hmoment grid w hw n r h (by omega) (by omega) hh removed hremoved i q p hshift
  have hs := hsurvival grid w hw n r h hn hr hh hsmall removed hremoved i q p hpp hshift
  have hm1 := hm.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have hex := sum_exp_neg_le_twice_min
    (x := (w n).rate i*Real.log ((n : ℝ)/(h : ℝ)))
    (y := Real.sqrt ((n : ℝ)*(h : ℝ))) hd.le
  have hm2 : (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      2*(p.factorial : ℝ)*(B*((w n).rate i/(h : ℝ)))^p*
        Real.exp (-d*min ((w n).rate i*Real.log ((n : ℝ)/(h : ℝ)))
          (Real.sqrt ((n : ℝ)*(h : ℝ)))) := by
    have hh := hm1.trans (mul_le_mul_of_nonneg_left hex (by positivity))
    nlinarith only [hh]
  have hpower := hm2.trans (uniform_moment_decay hpp hpp0 hB.le
    (by positivity) hd.le (le_min hx hy))
  have hnorm := deleted_kernel_eLpNorm_le_of_moment (w n) removed i q.val p (by omega)
    (by positivity) hpower
  apply hnorm.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (exp_neg_min_le_sum (d/(p0 : ℝ))
    ((w n).rate i*Real.log ((n : ℝ)/(h : ℝ))) (Real.sqrt ((n : ℝ)*(h : ℝ))))
    (by positivity)

end Luce.Section6
