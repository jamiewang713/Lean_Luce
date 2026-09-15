import Luce.Section6OrderedInsertion

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators
namespace Luce.Section6

theorem measurable_orderedInsertionKernel {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) :
    Measurable (orderedInsertionKernel w u q) := by
  apply measurable_measure_prodMk_left (s :=
    {z : (Fin n → ℝ) × (Fin n → ℝ) | OrderedMarkedInsertion u q z.1 z.2})
  exact measurableSet_orderedMarkedInsertion u q Prod.fst Prod.snd
    (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp measurable_snd)

theorem orderedInsertionKernel_le_one {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (old : Fin n → ℝ) :
    orderedInsertionKernel w u q old ≤ 1 := prob_le_one

theorem orderedInsertionKernel_integrable {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) :
    Integrable (fun old => (orderedInsertionKernel w u q old).toReal) (exponentialRace w) := by
  apply integrable_toReal_of_lintegral_ne_top (measurable_orderedInsertionKernel w u q).aemeasurable
  exact ne_of_lt ((lintegral_mono (orderedInsertionKernel_le_one w u q)).trans_lt (by simp))

/-- A finite real expectation for arbitrary distinct marked ranks, including
adjacent ranks. Integrability is proved, not supplied by an input. -/
theorem markedRankCylinder_real_probability_eq_sortedOrderedInsertion {n r : ℕ}
    (w : Weights n) (u j : Fin r → Fin n) (hu : Injective u) (hj : Injective j) :
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} =
      ∫ old, (orderedInsertionKernel w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j) old).toReal
        ∂exponentialRace w := by
  have hm := measurable_orderedInsertionKernel w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j)
  have hfinite : ∀ old, orderedInsertionKernel w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j) old < ∞ :=
    fun old => (orderedInsertionKernel_le_one w _ _ old).trans_lt (by simp)
  rw [Measure.real, markedRankCylinder_probability_eq_sortedOrderedInsertion w u j hu hj,
    ← integral_toReal hm.aemeasurable (Filter.Eventually.of_forall hfinite)]

end Luce.Section6
