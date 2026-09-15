import Luce.Section6KernelLp

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Uniform bound for all insertion gaps, including the final gap. -/
theorem deleted_kernel_eLpNorm_le_one {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n) (k : ℕ) (p : ℝ≥0∞) :
    eLpNorm (fun old => (deletedGapKernel w removed old i k).toReal) p (exponentialRace w) ≤ 1 := by
  have hb : ∀ᵐ old ∂exponentialRace w, ‖(deletedGapKernel w removed old i k).toReal‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro old
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have he := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) (deletedGapKernel_le_one w removed old i k)
    simpa only [ENNReal.toReal_one] using he
  simpa using eLpNorm_le_of_ae_bound (p := p) hb

end Luce.Section6
