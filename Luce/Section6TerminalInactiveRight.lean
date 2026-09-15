import Luce.Section6TerminalLogarithmicLp
import Luce.Section6BoundedTerminalKernel
import Luce.Section6InactiveBounds

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The inactive-right kernel across a fixed terminal window, including the
infinite final gap. The reference gap and positive rate floor are constructed. -/
theorem PowerProfile.terminal_inactive_right_envelope {f : ℝ → ℝ}
    {left : EndpointBehavior} {c : ℝ} (hp : PowerProfile f left (.finite c))
    (r Q p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < d ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, N ≤ n → 1 ≤ m → m ≤ Q+1 →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (k p : ℕ), (Finset.univ \ removed).card ≤ k+Q →
    1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i k).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*(((w n).rate i/(m : ℝ))*
        Real.exp (-d*((w n).rate i*Real.log ((n : ℝ)/(m : ℝ))))+
          Real.exp (-d*Real.sqrt ((n : ℝ)*(m : ℝ))))) := by
  obtain ⟨B, d, hB, hd, hb⟩ := terminal_logarithmic_insertion_Lp hp.1 hp.2.1 p0 hp0
  obtain ⟨b, hbp, hrate⟩ := hp.global_lower_of_right_finite
  let H : ℕ := 8*r+Q+8
  refine ⟨B*(1+(H : ℝ)/b), d/2, 16384*H+H^2, by positivity, half_pos hd,
    by dsimp [H]; omega, ?_⟩
  intro grid w hw n m hn hm hmQ removed hremoved i k p hk hpp hpp0
  have hH : 8*r+Q+8 ≤ H := le_rfl
  have hsmall : 16384*H ≤ n := by omega
  have hn8 : 8 ≤ n := by dsimp [H] at *; omega
  have hnr : 16*r ≤ n := by dsimp [H] at *; omega
  apply (hb grid w hw n r Q H hn8 hnr hH hsmall removed hremoved i k p hk hpp hpp0).trans
  apply ENNReal.ofReal_le_ofReal
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by dsimp [H]; omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmH : (m : ℝ) ≤ H := by exact_mod_cast (show m ≤ H by dsimp [H]; omega)
  have hHn : (H : ℝ)^2 ≤ n := by exact_mod_cast (show H^2 ≤ n by omega)
  have hbi : b ≤ (w n).rate i := by rw [hw n i]; exact hrate _ (samplePoint_mem grid i)
  have he := bounded_terminal_logarithmic_kernel hH1 hm1 hmH hHn hbp hbi hd
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he hB.le

end Luce.Section6
