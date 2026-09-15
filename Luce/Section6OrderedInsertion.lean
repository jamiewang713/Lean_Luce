import Luce.Section5MarkedSort

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- Exact insertion with shared gaps: the marked time order must be retained. -/
theorem markedRankCylinder_iff_ordered_counts {n r : ℕ} (u j : Fin r → Fin n)
    (hu : Injective u) (hj : StrictMono j) (q : Fin r → ℕ)
    (hindex : ∀ a, q a+a.val = (j a).val) (clocks : Fin n → ℝ) :
    MarkedRankCylinder u j clocks ↔
      StrictMono (fun a => clocks (u a)) ∧
      ∀ a, deletedBeforeCount (Finset.univ.image u) clocks (clocks (u a)) = q a := by
  constructor
  · intro h
    refine ⟨marked_times_strictMono_of_rankCylinder u j clocks hj h, ?_⟩
    intro a
    have hh := markedRankCylinder_deleted_counts u j hu hj clocks h a
    have hi := hindex a
    omega
  · rintro ⟨horder, hcount⟩ a
    have hh := clockBeforeCount_eq_deleted_add_marked u hu clocks (clocks (u a))
    rw [markedBeforeCount_eq_index u clocks horder a, hcount a, hindex a] at hh
    change 1+clockBeforeCount clocks (clocks (u a)) = (j a).val+1
    omega

/-- The literal ordered insertion region in fresh marked coordinates.
Count-gap membership also covers the first and terminal gaps. -/
def OrderedMarkedInsertion {n r : ℕ} (u : Fin r → Fin n) (q : Fin r → ℕ)
    (old fresh : Fin n → ℝ) : Prop :=
  StrictMono (fun a => fresh (u a)) ∧
    ∀ a, DeletedGapCount (Finset.univ.image u) old (q a) (fresh (u a))

/-- Its conditional mass uses the original independent exponential laws.
It has not been replaced by independent rank events. -/
def orderedInsertionKernel {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (old : Fin n → ℝ) : ℝ≥0∞ :=
  exponentialRace w {fresh | OrderedMarkedInsertion u q old fresh}

theorem measurableSet_orderedMarkedInsertion {Ω : Type*} [MeasurableSpace Ω]
    {n r : ℕ} (u : Fin r → Fin n) (q : Fin r → ℕ)
    (old fresh : Ω → Fin n → ℝ)
    (ho : ∀ i, Measurable (fun z => old z i))
    (hf : ∀ i, Measurable (fun z => fresh z i)) :
    MeasurableSet {z | OrderedMarkedInsertion u q (old z) (fresh z)} := by
  unfold OrderedMarkedInsertion
  apply MeasurableSet.inter
  · change MeasurableSet {z | ∀ a b : Fin r, a < b → fresh z (u a) < fresh z (u b)}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    apply MeasurableSet.iInter
    intro b
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt (hf (u a)) (hf (u b))
  · change MeasurableSet {z | ∀ a, DeletedGapCount (Finset.univ.image u) (old z) (q a) (fresh z (u a))}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    exact measurableSet_deletedGapCount (Finset.univ.image u) old (q a)
      (fun z => fresh z (u a)) ho (hf (u a))

theorem orderedInsertionKernel_le_product {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (hu : Injective u) (old : Fin n → ℝ) :
    orderedInsertionKernel w u q old ≤
      ∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a) := by
  rw [← deletedGapKernel_marked_product w old u q hu]
  exact measure_mono (fun _ h => h.2)

theorem swapped_rankCylinder_iff_ordered_insertion {n r : ℕ}
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r → ℕ) (hindex : ∀ a, q a+a.val = (j a).val)
    (c : Fin n → ℝ × ℝ)
    (hpos : ∀ i, 0 < (swapClockCopies (Finset.univ.image u) c i).1) :
    MarkedRankCylinder u j (fun i => (swapClockCopies (Finset.univ.image u) c i).1) ↔
      OrderedMarkedInsertion u q (fun i => (c i).1) (fun i => (c i).2) := by
  rw [markedRankCylinder_iff_ordered_counts u j hu hj q hindex]
  have hmark (a : Fin r) : (swapClockCopies (Finset.univ.image u) c (u a)).1 = (c (u a)).2 := by
    simp [swapClockCopies]
  simp_rw [swapped_deleted_count, hmark]
  constructor
  · rintro ⟨ho, hc⟩
    refine ⟨ho, fun a => ⟨?_, hc a⟩⟩
    simpa only [hmark a] using hpos (u a)
  · rintro ⟨ho, hc⟩
    exact ⟨ho, fun a => (hc a).2⟩

/-- Exact conditional ordered-region identity, without gap separation.
Factorization into one simplex per repeated gap is a subsequent obligation. -/
theorem markedRankCylinder_probability_eq_orderedInsertion {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r → ℕ) (hindex : ∀ a, q a+a.val = (j a).val) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} =
      ∫⁻ old, orderedInsertionKernel w u q old ∂exponentialRace w := by
  let A := {z : (Fin n → ℝ) × (Fin n → ℝ) | OrderedMarkedInsertion u q z.1 z.2}
  have hA : MeasurableSet A := measurableSet_orderedMarkedInsertion u q Prod.fst Prod.snd
    (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp measurable_snd)
  have htonelli : (∫⁻ old, orderedInsertionKernel w u q old ∂exponentialRace w) =
      pairedExponentialRace w {c | OrderedMarkedInsertion u q (fun i => (c i).1) (fun i => (c i).2)} := by
    calc
      _ = ((exponentialRace w).prod (exponentialRace w)) A := (Measure.prod_apply hA).symm
      _ = pairedExponentialRace w
          ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) ⁻¹' A) :=
        ((pairedExponentialRace_families w).measure_preimage hA.nullMeasurableSet).symm
      _ = _ := rfl
  rw [htonelli]
  calc
    _ = pairedExponentialRace w {c | MarkedRankCylinder u j
        (fun i => (swapClockCopies (Finset.univ.image u) c i).1)} :=
      ((swapped_background_measurePreserving w (Finset.univ.image u)).measure_preimage
        (measurableSet_markedRankCylinder u j).nullMeasurableSet).symm
    _ = _ := by
      apply measure_congr
      filter_upwards [(swapped_background_measurePreserving w (Finset.univ.image u)).quasiMeasurePreserving.ae
        (exponentialRace_positive_background w)] with c hc
      exact propext (swapped_rankCylinder_iff_ordered_insertion u j hu hj q hindex c hc)

/-- Arbitrary distinct targets are sorted, with q=j-b derived exactly.
No minimum separation of target ranks is required. -/
theorem markedRankCylinder_probability_eq_sortedOrderedInsertion {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : Injective j) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} =
      ∫⁻ old, orderedInsertionKernel w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j) old
        ∂exponentialRace w := by
  have h := markedRankCylinder_probability_eq_orderedInsertion w (u ∘ Tuple.sort j)
    (j ∘ Tuple.sort j) (hu.comp (Tuple.sort j).injective)
    (strictMono_sorted_markedRanks j hj) (sortedMarkedGapIndex j)
    (sortedMarkedGapIndex_add j hj)
  simpa only [markedRankCylinder_comp_perm] using h

end Luce.Section6
