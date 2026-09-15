import Luce.Section6GapStartTail
import Luce.Section6KernelLp

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

theorem gapStart_lt_of_beforeCount {n : ℕ} (old : Fin n → ℝ)
    (hi : Function.Injective old) (q : Fin n) {t : ℝ} (ht : 0 < t)
    (hq : q.val ≤ clockBeforeCount old t) : raceGapStart old q < t := by
  rw [raceGapStart_eq_consecutiveGapLower old hi]
  unfold consecutiveGapLower
  split_ifs with hzero
  · exact ht
  · apply (arrivalTime_lt_iff_clockBeforeCount old hi ⟨q.val-1, by omega⟩ t).mpr
    simp only [Fin.val_mk]
    omega

/-- Every later insertion gap lies above an earlier finite gap start.
The later index k is a natural number and may be the final infinite gap. -/
theorem deletedGapKernel_le_earlier_survival {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ)
    (hold : Function.Injective old) (hpos : ∀ i, 0 ≤ old i)
    (i : Fin n) (q : Fin (Finset.univ \ removed).card) (k : ℕ) (hqk : q.val ≤ k) :
    deletedGapKernel w removed old i k ≤ ENNReal.ofReal
      (Real.exp (-(w.rate i*raceGapStart (compactDeletedClocks removed old) q))) := by
  have hc := compactDeletedClocks_injective removed old hold
  have hs : 0 ≤ raceGapStart (compactDeletedClocks removed old) q := by
    rw [raceGapStart_eq_consecutiveGapLower _ hc]
    exact consecutiveGapLower_nonneg _ hc (fun j => hpos _) q
  rw [← expMeasure_Ioi (w.positive i) hs]
  apply measure_mono
  intro t ht
  apply gapStart_lt_of_beforeCount _ hc q ht.1
  rw [clockBeforeCount_compactDeletedClocks, ht.2]
  exact hqk

theorem deletedGapKernel_le_earlier_survival_ae {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n)
    (q : Fin (Finset.univ \ removed).card) (k : ℕ) (hqk : q.val ≤ k) :
    ∀ᵐ old ∂exponentialRace w, (deletedGapKernel w removed old i k).toReal ≤
      Real.exp (-(w.rate i*raceGapStart (compactDeletedClocks removed old) q)) := by
  filter_upwards [exponentialRace_injective_ae w, exponentialRace_nonnegative_background w]
    with old hi hn
  have hb := ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
    (deletedGapKernel_le_earlier_survival w removed old hi hn i q k hqk)
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using hb

/-- Moments of any later gap, including the infinite final gap, are bounded
by the survival moment at the finite reference gap. -/
theorem deleted_gap_moment_le_earlier_survival {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n)
    (q : Fin (Finset.univ \ removed).card) (k p : ℕ) (hqk : q.val ≤ k) :
    (∫ old, (deletedGapKernel w removed old i k).toReal^p ∂exponentialRace w) ≤
      ∫ old, Real.exp (-((p : ℝ)*w.rate i*
        raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace w := by
  apply integral_mono_ae (deleted_kernel_power_integrable w removed i k p)
    (deleted_survival_integrable w removed i q p)
  filter_upwards [deletedGapKernel_le_earlier_survival_ae w removed i q k hqk] with old hb
  have he := pow_le_pow_left₀ ENNReal.toReal_nonneg hb p
  have hid : (Real.exp (-(w.rate i*raceGapStart (compactDeletedClocks removed old) q)))^p =
      Real.exp (-((p : ℝ)*w.rate i*raceGapStart (compactDeletedClocks removed old) q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [hid] at he

end Luce.Section6
