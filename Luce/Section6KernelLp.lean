import Luce.Section6ModerateInsertionMoment

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The actual insertion probability is bounded by one, so every Lp norm
exists without an additional integrability hypothesis. -/
theorem deleted_kernel_memLp {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n) (q : ℕ) (p : ℝ≥0∞) :
    MemLp (fun old => (deletedGapKernel w removed old i q).toReal) p (exponentialRace w) := by
  apply MemLp.of_bound
    (measurable_deletedGapKernel w removed i q).ennreal_toReal.aestronglyMeasurable (1 : ℝ)
  refine Filter.Eventually.of_forall (fun old => ?_)
  change ‖(deletedGapKernel w removed old i q).toReal‖ ≤ (1 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_le_toReal
    (ne_of_lt ((deletedGapKernel_le_one w removed old i q).trans_lt (by simp))) (by simp)).mpr
    (deletedGapKernel_le_one w removed old i q)

theorem deleted_kernel_eLpNorm_eq_moment {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n) (q p : ℕ) (hp : 0 < p) :
    eLpNorm (fun old => (deletedGapKernel w removed old i q).toReal) (p : ℝ≥0∞)
      (exponentialRace w) = ENNReal.ofReal
        ((∫ old, (deletedGapKernel w removed old i q).toReal^p ∂exponentialRace w)^((p : ℝ)⁻¹)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hp.ne') (by simp)
    (deleted_kernel_memLp w removed i q p)]
  simp only [ENNReal.toReal_natCast, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    Real.rpow_natCast]

/-- A generic moment-to-norm step. Its sole analytic premise is discharged
by the concrete moderate moment theorem when used for sampled profiles. -/
theorem deleted_kernel_eLpNorm_le_of_moment {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n) (q p : ℕ) (hp : 0 < p)
    {K : ℝ} (hK : 0 ≤ K)
    (hm : (∫ old, (deletedGapKernel w removed old i q).toReal^p ∂exponentialRace w) ≤ K^p) :
    eLpNorm (fun old => (deletedGapKernel w removed old i q).toReal) (p : ℝ≥0∞)
      (exponentialRace w) ≤ ENNReal.ofReal K := by
  rw [deleted_kernel_eLpNorm_eq_moment w removed i q p hp]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (K^p)^((p : ℝ)⁻¹) := Real.rpow_le_rpow
      (integral_nonneg (fun _ => pow_nonneg ENNReal.toReal_nonneg p)) hm (by positivity)
    _ = K := Real.pow_rpow_inv_natCast hK hp.ne'

end Luce.Section6
