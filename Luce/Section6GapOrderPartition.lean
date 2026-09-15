import Luce.Section6OrderedInsertionExpectation

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- Subtracting the marked position from sorted full ranks leaves
nondecreasing gap numbers; repeated values are permitted. -/
theorem sortedMarkedGapIndex_monotone {n r : ℕ} (j : Fin r → Fin n)
    (hj : Injective j) : Monotone (sortedMarkedGapIndex j) := by
  let v := j ∘ Tuple.sort j
  have hv : StrictMono v := strictMono_sorted_markedRanks j hj
  intro a b hab
  have hsub : (Finset.Ico a b).image v ⊆ Finset.Ico (v a) (v b) := by
    intro i hi
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hi
    have hh := Finset.mem_Ico.mp hc
    exact Finset.mem_Ico.mpr ⟨hv.monotone hh.1, hv hh.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hv.injective, Fin.card_Ico, Fin.card_Ico] at hcard
  have ha := sortedMarkedGapIndex_add j hj a
  have hb := sortedMarkedGapIndex_add j hj b
  have hvab : (v a).val ≤ (v b).val := hv.monotone hab
  change b.val-a.val ≤ (v b).val-(v a).val at hcard
  change sortedMarkedGapIndex j a+a.val = (v a).val at ha
  change sortedMarkedGapIndex j b+b.val = (v b).val at hb
  have hab' : a.val ≤ b.val := hab
  omega

/-- One ordered simplex region, expressed in the actual count gap.
Its only fresh coordinates are the marked labels assigned to gap k. -/
def GapOrderedInsertion {n r : ℕ} (u : Fin r → Fin n) (q : Fin r → ℕ)
    (k : ℕ) (old fresh : Fin n → ℝ) : Prop :=
  (∀ a, q a = k → DeletedGapCount (Finset.univ.image u) old k (fresh (u a))) ∧
  ∀ a b, q a = k → q b = k → a < b → fresh (u a) < fresh (u b)

def gapOrderedKernel {n r : ℕ} (w : Weights n) (u : Fin r → Fin n)
    (q : Fin r → ℕ) (k : ℕ) (old : Fin n → ℝ) : ℝ≥0∞ :=
  exponentialRace w {fresh | GapOrderedInsertion u q k old fresh}

theorem measurableSet_gapOrderedInsertion {Ω : Type*} [MeasurableSpace Ω]
    {n r : ℕ} (u : Fin r → Fin n) (q : Fin r → ℕ) (k : ℕ)
    (old fresh : Ω → Fin n → ℝ)
    (ho : ∀ i, Measurable (fun z => old z i))
    (hf : ∀ i, Measurable (fun z => fresh z i)) :
    MeasurableSet {z | GapOrderedInsertion u q k (old z) (fresh z)} := by
  unfold GapOrderedInsertion
  apply MeasurableSet.inter
  · change MeasurableSet {z | ∀ a, q a = k →
      DeletedGapCount (Finset.univ.image u) (old z) k (fresh z (u a))}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_deletedGapCount (Finset.univ.image u) old k
      (fun z => fresh z (u a)) ho (hf (u a))
  · change MeasurableSet {z | ∀ a b, q a = k → q b = k → a < b → fresh z (u a) < fresh z (u b)}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    apply MeasurableSet.iInter
    intro b
    apply MeasurableSet.iInter
    intro _
    apply MeasurableSet.iInter
    intro _
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt (hf (u a)) (hf (u b))

theorem measurable_gapOrderedKernel {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (k : ℕ) :
    Measurable (gapOrderedKernel w u q k) := by
  apply measurable_measure_prodMk_left (s :=
    {z : (Fin n → ℝ) × (Fin n → ℝ) | GapOrderedInsertion u q k z.1 z.2})
  exact measurableSet_gapOrderedInsertion u q k Prod.fst Prod.snd
    (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp measurable_snd)

theorem gapOrderedKernel_le_one {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (k : ℕ) (old : Fin n → ℝ) :
    gapOrderedKernel w u q k old ≤ 1 := prob_le_one

/-- Ordering between different gaps follows from the actual before-count;
only within-gap ordering remains as a simplex restriction. -/
theorem orderedMarkedInsertion_iff_gap_partition {n r : ℕ}
    (u : Fin r → Fin n) (q : Fin r → ℕ) (hq : Monotone q)
    (old fresh : Fin n → ℝ) :
    OrderedMarkedInsertion u q old fresh ↔
      ∀ k ∈ Finset.univ.image q, GapOrderedInsertion u q k old fresh := by
  constructor
  · rintro ⟨ho, hc⟩ k _
    refine ⟨?_, fun a b _ _ hab => ho hab⟩
    intro a ha
    simpa only [ha] using hc a
  · intro h
    have hc (a : Fin r) : DeletedGapCount (Finset.univ.image u) old (q a) (fresh (u a)) :=
      (h (q a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)).1 a rfl
    refine ⟨?_, hc⟩
    intro a b hab
    by_cases heq : q a = q b
    · exact (h (q a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)).2
        a b rfl heq.symm hab
    · have hqab : q a < q b := lt_of_le_of_ne (hq hab.le) heq
      by_contra hle
      have hh := deletedBeforeCount_mono (Finset.univ.image u) old (le_of_not_gt hle)
      rw [(hc a).2, (hc b).2] at hh
      exact (not_le_of_gt hqab) hh

/-- Disjoint gap blocks depend on disjoint marked labels. -/
theorem gap_label_blocks_disjoint {n r : ℕ} (u : Fin r → Fin n)
    (hu : Injective u) (q : Fin r → ℕ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint ((Finset.univ.filter fun a => q a = k).image u)
      ((Finset.univ.filter fun a => q a = l).image u) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨a, ha, hai⟩ := Finset.mem_image.mp hi
  obtain ⟨b, hb, hbi⟩ := Finset.mem_image.mp hj
  have hab := hu (hai.trans hbi.symm)
  subst b
  exact hkl ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)

theorem gapOrderedInsertion_congr_on_block {n r : ℕ}
    (u : Fin r → Fin n) (q : Fin r → ℕ) (k : ℕ)
    (old fresh fresh' : Fin n → ℝ)
    (heq : ∀ a, q a = k → fresh (u a) = fresh' (u a)) :
    GapOrderedInsertion u q k old fresh ↔ GapOrderedInsertion u q k old fresh' := by
  constructor
  · rintro ⟨hc, ho⟩
    constructor
    · intro a ha
      rw [← heq a ha]
      exact hc a ha
    · intro a b ha hb hab
      rw [← heq a ha, ← heq b hb]
      exact ho a b ha hb hab
  · rintro ⟨hc, ho⟩
    constructor
    · intro a ha
      rw [heq a ha]
      exact hc a ha
    · intro a b ha hb hab
      rw [heq a ha, heq b hb]
      exact ho a b ha hb hab

/-- With distinct ordered gaps the simplex restrictions disappear entirely. -/
theorem orderedInsertionKernel_eq_product_of_strictMono {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (hu : Injective u) (hq : StrictMono q)
    (old : Fin n → ℝ) :
    orderedInsertionKernel w u q old =
      ∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a) := by
  rw [← deletedGapKernel_marked_product w old u q hu]
  unfold orderedInsertionKernel
  congr 1
  ext fresh
  constructor
  · exact fun h => h.2
  · intro hc
    refine ⟨?_, hc⟩
    intro a b hab
    by_contra hle
    have hh := deletedBeforeCount_mono (Finset.univ.image u) old (le_of_not_gt hle)
    rw [(hc a).2, (hc b).2] at hh
    exact (not_le_of_gt (hq hab)) hh

end Luce.Section6
