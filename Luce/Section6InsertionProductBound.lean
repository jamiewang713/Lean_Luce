import Luce.Section6GapOrderPartition
import Luce.Section6OrderedInsertionExpectation

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal
namespace Luce.Section6

theorem deleted_kernel_product_integrable {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n) (q : Fin r → ℕ) :
    Integrable (fun old => ∏ a, (deletedGapKernel w removed old (u a) (q a)).toReal)
      (exponentialRace w) := by
  have hm : Measurable (fun old => ∏ a, deletedGapKernel w removed old (u a) (q a)) :=
    Finset.measurable_prod _ (fun a _ => measurable_deletedGapKernel w removed (u a) (q a))
  have hle (old : Fin n → ℝ) : (∏ a, deletedGapKernel w removed old (u a) (q a)) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => zero_le) (fun a _ => deletedGapKernel_le_one w removed old (u a) (q a))
  have hi := integrable_toReal_of_lintegral_ne_top (μ := exponentialRace w) hm.aemeasurable
    (ne_of_lt ((lintegral_mono hle).trans_lt (by simp)))
  simpa only [ENNReal.toReal_prod] using hi

/-- Actual marked-cylinder probability bounded by the expectation of the
single-insertion factors. No rank separation or independence premise. -/
theorem markedRankCylinder_real_probability_le_gap_product {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : Injective j) :
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} ≤
      ∫ old, ∏ a, (deletedGapKernel w (Finset.univ.image (u ∘ Tuple.sort j)) old
        ((u ∘ Tuple.sort j) a) (sortedMarkedGapIndex j a)).toReal ∂exponentialRace w := by
  rw [markedRankCylinder_real_probability_eq_sortedOrderedInsertion w u j hu hj]
  apply integral_mono (orderedInsertionKernel_integrable w _ _)
    (deleted_kernel_product_integrable w _ _ _)
  intro old
  dsimp only
  rw [← ENNReal.toReal_prod]
  apply ENNReal.toReal_mono
  · exact ne_of_lt ((Finset.prod_le_one (fun _ _ => zero_le)
      (fun a _ => deletedGapKernel_le_one w _ old _ _)).trans_lt (by simp))
  · exact orderedInsertionKernel_le_product w _ _ (hu.comp (Tuple.sort j).injective) old

end Luce.Section6
