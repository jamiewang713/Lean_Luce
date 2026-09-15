import Luce.Section6InsertionProductBound
import Mathlib.MeasureTheory.Integral.MeanInequalities

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal
namespace Luce.Section6

/-- Finite Holder inequality for the actual insertion factors. Their shared
background may create dependence; no independence is used or assumed. -/
theorem deleted_kernel_product_le_Lp {n r : ℕ} (w : Weights n) (hr : 0 < r)
    (removed : Finset (Fin n)) (u : Fin r → Fin n) (q : Fin r → ℕ) :
    (∫⁻ old, ∏ a, deletedGapKernel w removed old (u a) (q a) ∂exponentialRace w) ≤
      ∏ a, eLpNorm (fun old => (deletedGapKernel w removed old (u a) (q a)).toReal)
        (r : ℝ≥0∞) (exponentialRace w) := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hs : (∑ _a : Fin r, (r : ℝ)⁻¹) = 1 := by simp [hr.ne']
  have hholder := ENNReal.lintegral_prod_norm_pow_le (μ := exponentialRace w) Finset.univ
    (f := fun a : Fin r => fun old => (deletedGapKernel w removed old (u a) (q a))^(r : ℝ))
    (fun a _ => ((measurable_deletedGapKernel w removed (u a) (q a)).aemeasurable.pow_const _))
    (p := fun _ => (r : ℝ)⁻¹) hs (fun _ _ => inv_nonneg.mpr hrR.le)
  have hn (a : Fin r) (old : Fin n → ℝ) :
      ‖(deletedGapKernel w removed old (u a) (q a)).toReal‖ₑ =
        deletedGapKernel w removed old (u a) (q a) :=
    Real.enorm_toReal (ne_of_lt ((deletedGapKernel_le_one w removed old (u a) (q a)).trans_lt (by simp)))
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (r : ℝ≥0∞)) (by exact_mod_cast hr.ne') (by simp),
    ENNReal.toReal_natCast, hn]
  simpa only [← ENNReal.rpow_mul, mul_inv_cancel₀ hrR.ne', ENNReal.rpow_one, one_div] using hholder

/-- The concrete cylinder-to-Lp product bound, including adjacent demanded
ranks and repeated sorted gap indices. All finite-law premises are proved. -/
theorem markedRankCylinder_probability_le_Lp_product {n r : ℕ} (w : Weights n) (hr : 0 < r)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : Injective j) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} ≤
      ∏ a, eLpNorm (fun old => (deletedGapKernel w (Finset.univ.image (u ∘ Tuple.sort j)) old
        ((u ∘ Tuple.sort j) a) (sortedMarkedGapIndex j a)).toReal)
        (r : ℝ≥0∞) (exponentialRace w) := by
  rw [markedRankCylinder_probability_eq_sortedOrderedInsertion w u j hu hj]
  exact (lintegral_mono (orderedInsertionKernel_le_product w _ _
    (hu.comp (Tuple.sort j).injective))).trans (deleted_kernel_product_le_Lp w hr _ _ _)

end Luce.Section6
