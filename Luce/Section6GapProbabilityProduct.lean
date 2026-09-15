import Luce.Section6DisjointClockEvents

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- The full conditional product over occupied gaps, allowing several
marked clocks in the same gap. Each factor keeps its internal ordering. -/
theorem orderedInsertionKernel_eq_gap_product {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (hu : Injective u) (hq : Monotone q)
    (old : Fin n → ℝ) :
    orderedInsertionKernel w u q old =
      ∏ k ∈ Finset.univ.image q, gapOrderedKernel w u q k old := by
  let block := fun k => (Finset.univ.filter fun a => q a = k).image u
  let A := fun k => {fresh : Fin n → ℝ | GapOrderedInsertion u q k old fresh}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurableSet_gapOrderedInsertion u q k (fun _ => old) id
      (fun _ => measurable_const) (fun i => measurable_pi_apply i)
  have hsupport : ∀ k x y, (∀ i ∈ block k, x i = y i) → (x ∈ A k ↔ y ∈ A k) := by
    intro k x y he
    apply gapOrderedInsertion_congr_on_block u q k old x y
    intro a ha
    exact he (u a) (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩)
  have hdisjoint : ∀ k l, k ≠ l → Disjoint (block k) (block l) :=
    fun _ _ hkl => gap_label_blocks_disjoint u hu q hkl
  have hh := exponentialRace_biInter_disjoint_support w block A hA hsupport hdisjoint
    (Finset.univ.image q)
  have heq : {fresh | OrderedMarkedInsertion u q old fresh} =
      {fresh | ∀ k ∈ Finset.univ.image q, fresh ∈ A k} := by
    ext fresh
    exact orderedMarkedInsertion_iff_gap_partition u q hq old fresh
  unfold orderedInsertionKernel
  rw [heq]
  exact hh

/-- Exact cylinder expectation of ordered per-gap masses for arbitrary
distinct marked labels and targets. No gap/rank separation is required. -/
theorem markedRankCylinder_probability_eq_gap_product {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : Injective j) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} =
      ∫⁻ old, ∏ k ∈ Finset.univ.image (sortedMarkedGapIndex j),
        gapOrderedKernel w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j) k old
        ∂exponentialRace w := by
  rw [markedRankCylinder_probability_eq_sortedOrderedInsertion w u j hu hj]
  apply lintegral_congr
  intro old
  exact orderedInsertionKernel_eq_gap_product w _ _ (hu.comp (Tuple.sort j).injective)
    (sortedMarkedGapIndex_monotone j hj) old

theorem gapOrderedProduct_integrable {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) :
    Integrable (fun old => ∏ k ∈ Finset.univ.image q, (gapOrderedKernel w u q k old).toReal)
      (exponentialRace w) := by
  have hm : Measurable (fun old => ∏ k ∈ Finset.univ.image q, gapOrderedKernel w u q k old) :=
    Finset.measurable_prod _ (fun k _ => measurable_gapOrderedKernel w u q k)
  have hle (old : Fin n → ℝ) : (∏ k ∈ Finset.univ.image q, gapOrderedKernel w u q k old) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => zero_le) (fun k _ => gapOrderedKernel_le_one w u q k old)
  have hh := integrable_toReal_of_lintegral_ne_top (μ := exponentialRace w) hm.aemeasurable
    (ne_of_lt ((lintegral_mono hle).trans_lt (by simp)))
  simpa only [ENNReal.toReal_prod] using hh

theorem markedRankCylinder_real_probability_eq_gap_product {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : Injective j) :
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} =
      ∫ old, ∏ k ∈ Finset.univ.image (sortedMarkedGapIndex j),
        (gapOrderedKernel w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j) k old).toReal
        ∂exponentialRace w := by
  have hm : Measurable (fun old => ∏ k ∈ Finset.univ.image (sortedMarkedGapIndex j),
      gapOrderedKernel w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j) k old) :=
    Finset.measurable_prod _ (fun k _ => measurable_gapOrderedKernel w _ _ k)
  have hfinite : ∀ old, (∏ k ∈ Finset.univ.image (sortedMarkedGapIndex j),
      gapOrderedKernel w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j) k old) < ∞ := by
    intro old
    exact (Finset.prod_le_one (fun _ _ => zero_le)
      (fun k _ => gapOrderedKernel_le_one w _ _ k old)).trans_lt (by simp)
  rw [Measure.real, markedRankCylinder_probability_eq_gap_product w u j hu hj,
    ← integral_toReal hm.aemeasurable (Filter.Eventually.of_forall hfinite)]
  simp only [ENNReal.toReal_prod]

end Luce.Section6
