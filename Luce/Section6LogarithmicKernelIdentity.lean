import Luce.Section6InactiveRightAllGaps

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Exact conversion between logarithmic and real-power terminal kernels. -/
theorem exp_neg_rate_log_ratio {n m : ℝ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    Real.exp (-t*Real.log (n/m)) = (m/n)^t := by
  rw [Real.rpow_def_of_pos (div_pos hm hn)]
  congr 1
  rw [Real.log_div hn.ne' hm.ne', Real.log_div hm.ne' hn.ne']
  ring

/-- The literal inactive terminal kernel in eq:sp-inactive-terminal-kernel,
uniform over all bounded-deletion gap shifts, including the final gap. -/
theorem PowerProfile.inactive_right_all_gaps_power_kernel {f : ℝ → ℝ}
    {left : EndpointBehavior} {c : ℝ} (hp : PowerProfile f left (.finite c))
    (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < d ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, N ≤ n → 1 ≤ h → 16384*h ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q p : ℕ), Nat.dist q (n-h) ≤ r+1 → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*(((w n).rate i/(h : ℝ))*
        ((h : ℝ)/(n : ℝ))^(d*(w n).rate i)+
          Real.exp (-d*Real.sqrt ((n : ℝ)*(h : ℝ))))) := by
  obtain ⟨C, d, N, hC, hd, hN, hb⟩ := hp.inactive_right_all_gaps_envelope r p0 hp0
  refine ⟨C, d, N, hC, hd, hN, ?_⟩
  intro grid w hw n h hn hh hregion removed hremoved i q p hshift hpp hpp0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hid : Real.exp (-d*((w n).rate i*Real.log ((n : ℝ)/(h : ℝ)))) =
      ((h : ℝ)/(n : ℝ))^(d*(w n).rate i) := by
    rw [← exp_neg_rate_log_ratio hnR hhR]
    congr 1
    ring
  simpa only [hid] using hb grid w hw n h hn hh hregion removed hremoved i q p hshift hpp hpp0

end Luce.Section6
