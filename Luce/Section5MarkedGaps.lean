import Luce.Section5GhostCylinder
import Mathlib.Order.Interval.Finset.Fin

/-!
# Exact insertion of marked clocks into deleted gaps

Source: `fixed_points.tex:1017–1048`. Labels are ordered by their prescribed
ranks. If `a : Fin r` is the zero-based position in that ordering and `j a`
is the zero-based full rank, then the deleted gap has index `j a - a`.
Unlike ghost windows, these are exact consecutive deleted-clock gaps.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

/-- Unmarked clocks strictly before an insertion time. -/
def deletedBeforeCount {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (t : ℝ) : ℕ :=
  ((Finset.univ \ removed).filter fun i => old i < t).card

lemma deletedBeforeCount_mono {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) : Monotone (deletedBeforeCount removed old) := by
  intro s t hst
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
    ((Finset.mem_filter.mp hi).2).trans_le hst⟩

lemma deletedBeforeCount_eq_of_eq_off {n : ℕ} (removed : Finset (Fin n))
    (old new : Fin n → ℝ) (hsame : ∀ i, i ∉ removed → new i = old i) (t : ℝ) :
    deletedBeforeCount removed new t = deletedBeforeCount removed old t := by
  unfold deletedBeforeCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  rw [hsame i (Finset.mem_sdiff.mp hi).2]

/-- Exact accounting for every marked clock; injectivity discharges all
image multiplicities. -/
lemma clockBeforeCount_eq_deleted_add_marked {n r : ℕ} (u : Fin r → Fin n)
    (hu : Injective u) (clocks : Fin n → ℝ) (t : ℝ) :
    clockBeforeCount clocks t = deletedBeforeCount (Finset.univ.image u) clocks t +
      ∑ a : Fin r, if clocks (u a) < t then 1 else 0 := by
  have h := Finset.sum_sdiff (Finset.subset_univ (Finset.univ.image u))
    (f := fun i => if clocks i < t then (1 : ℕ) else 0)
  simp only [clockBeforeCount, deletedBeforeCount, Finset.card_filter]
  rw [← h, Finset.sum_image]
  exact fun a _ b _ hab => hu hab

lemma markedBeforeCount_eq_index {n r : ℕ} (u : Fin r → Fin n)
    (clocks : Fin n → ℝ) (hordered : StrictMono (fun a => clocks (u a))) (a : Fin r) :
    (∑ b : Fin r, if clocks (u b) < clocks (u a) then 1 else 0) = a.val := by
  simp_rw [hordered.lt_iff_lt]
  rw [← Finset.card_filter]
  have heq : (Finset.univ.filter fun b : Fin r => b < a) = Finset.Iio a := by
    ext b
    simp
  rw [heq, Fin.card_Iio]

/-- Sorted prescribed ranks force sorted marked times, including for
arbitrary deterministic backgrounds. -/
lemma marked_times_strictMono_of_rankCylinder {n r : ℕ}
    (u j : Fin r → Fin n) (clocks : Fin n → ℝ)
    (hj : StrictMono j) (h : MarkedRankCylinder u j clocks) :
    StrictMono (fun a => clocks (u a)) := by
  intro a b hab
  by_contra hn
  have hc := clockBeforeCount_mono clocks (le_of_not_gt hn)
  change clockBeforeCount clocks (clocks (u b)) ≤ clockBeforeCount clocks (clocks (u a)) at hc
  have ha := h a
  have hb := h b
  have hjab : (j a).val < (j b).val := hj hab
  change 1 + clockBeforeCount clocks (clocks (u a)) = (j a).val + 1 at ha
  change 1 + clockBeforeCount clocks (clocks (u b)) = (j b).val + 1 at hb
  omega

/-- Deleting the `a` earlier marked clocks gives gap number `j_a-a`.
The one-based paper position is `a.val+1` and its rank is `(j a).val+1`. -/
theorem markedRankCylinder_deleted_counts {n r : ℕ} (u j : Fin r → Fin n)
    (hu : Injective u) (hj : StrictMono j) (clocks : Fin n → ℝ)
    (h : MarkedRankCylinder u j clocks) :
    ∀ a, deletedBeforeCount (Finset.univ.image u) clocks (clocks (u a)) =
      (j a).val - a.val := by
  have htimes := marked_times_strictMono_of_rankCylinder u j clocks hj h
  intro a
  have hc := clockBeforeCount_eq_deleted_add_marked u hu clocks (clocks (u a))
  rw [markedBeforeCount_eq_index u clocks htimes a] at hc
  have ha := h a
  change 1 + clockBeforeCount clocks (clocks (u a)) = (j a).val + 1 at ha
  omega

/-- Different ordered gap numbers force different ordered insertion times. -/
lemma marked_times_strictMono_of_deleted_counts {n r : ℕ}
    (u : Fin r → Fin n) (q : Fin r → ℕ) (hq : StrictMono q)
    (clocks : Fin n → ℝ)
    (h : ∀ a, deletedBeforeCount (Finset.univ.image u) clocks (clocks (u a)) = q a) :
    StrictMono (fun a => clocks (u a)) := by
  intro a b hab
  by_contra hn
  have hc := deletedBeforeCount_mono (Finset.univ.image u) clocks (le_of_not_gt hn)
  rw [h a, h b] at hc
  exact (not_le_of_gt (hq hab)) hc

/-- Exact deterministic insertion identity when the relevant deleted gaps
are distinct. The arithmetic identity exposes the rank convention rather
than relying on truncated subtraction. -/
theorem markedRankCylinder_iff_deleted_counts {n r : ℕ} (u j : Fin r → Fin n)
    (hu : Injective u) (hj : StrictMono j) (q : Fin r → ℕ)
    (hq : StrictMono q) (hindex : ∀ a, q a + a.val = (j a).val)
    (clocks : Fin n → ℝ) :
    MarkedRankCylinder u j clocks ↔
      ∀ a, deletedBeforeCount (Finset.univ.image u) clocks (clocks (u a)) = q a := by
  constructor
  · intro h a
    have hc := markedRankCylinder_deleted_counts u j hu hj clocks h a
    have hi := hindex a
    omega
  · intro h
    have ht := marked_times_strictMono_of_deleted_counts u q hq clocks h
    intro a
    have hc := clockBeforeCount_eq_deleted_add_marked u hu clocks (clocks (u a))
    rw [markedBeforeCount_eq_index u clocks ht a, h a, hindex a] at hc
    change 1 + clockBeforeCount clocks (clocks (u a)) = (j a).val + 1
    omega

lemma measurable_deletedBeforeCount {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (removed : Finset (Fin n)) (old : Ω → Fin n → ℝ) (t : Ω → ℝ)
    (hold : ∀ i, Measurable (fun x => old x i)) (ht : Measurable t) :
    Measurable (fun x => deletedBeforeCount removed (old x) (t x)) := by
  simp only [deletedBeforeCount, Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt (hold i) ht) measurable_const measurable_const

/-- Membership in the exact deleted gap, with both its endpoints excluded
almost surely. Endpoint correspondence is proved below. -/
def DeletedGapCount {n : ℕ} (removed : Finset (Fin n)) (old : Fin n → ℝ)
    (q : ℕ) (t : ℝ) : Prop := 0 < t ∧ deletedBeforeCount removed old t = q

lemma measurableSet_deletedGapCount {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (removed : Finset (Fin n)) (old : Ω → Fin n → ℝ) (q : ℕ) (t : Ω → ℝ)
    (hold : ∀ i, Measurable (fun x => old x i)) (ht : Measurable t) :
    MeasurableSet {x | DeletedGapCount removed (old x) q (t x)} :=
  (measurableSet_lt measurable_const ht).inter
    (measurableSet_eq_fun (measurable_deletedBeforeCount removed old t hold ht) measurable_const)

/-- Probability mass of a single exact deleted gap. -/
def deletedGapKernel {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (old : Fin n → ℝ) (i : Fin n) (q : ℕ) : ℝ≥0∞ :=
  expMeasure (w.rate i) {t | DeletedGapCount removed old q t}

lemma deletedGapKernel_le_one {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (old : Fin n → ℝ) (i : Fin n) (q : ℕ) : deletedGapKernel w removed old i q ≤ 1 := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  exact prob_le_one

lemma measurable_deletedGapKernel {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n) (q : ℕ) :
    Measurable (fun old => deletedGapKernel w removed old i q) := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  apply measurable_measure_prodMk_left (s :=
    {z : (Fin n → ℝ) × ℝ | DeletedGapCount removed z.1 q z.2})
  exact measurableSet_deletedGapCount removed Prod.fst q Prod.snd
    (fun k => (measurable_pi_apply k).comp measurable_fst) measurable_snd

/-- The exact deleted-gap mass product is a conditional probability. -/
theorem deletedGapKernel_marked_product {n r : ℕ} (w : Weights n)
    (old : Fin n → ℝ) (u : Fin r → Fin n) (q : Fin r → ℕ) (hu : Injective u) :
    exponentialRace w {fresh | ∀ a,
      DeletedGapCount (Finset.univ.image u) old (q a) (fresh (u a))} =
      ∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a) := by
  let sets := fun a : Fin r => {t | DeletedGapCount (Finset.univ.image u) old (q a) t}
  have hs : ∀ a, MeasurableSet (sets a) := fun a =>
    measurableSet_deletedGapCount (Finset.univ.image u) (fun _ => old) (q a) id
      (fun _ => measurable_const) measurable_id
  have h := ((exponentialRace_independent w).precomp hu).measure_inter_preimage_eq_mul
    Finset.univ (sets := sets) (fun a _ => hs a)
  simp only [Finset.mem_univ, iInter_true] at h
  have heq : (⋂ a, (fun fresh : Fin n → ℝ => fresh (u a)) ⁻¹' sets a) =
      {fresh | ∀ a, DeletedGapCount (Finset.univ.image u) old (q a) (fresh (u a))} := by
    ext fresh
    simp [sets]
  rw [← heq, h]
  apply Finset.prod_congr rfl
  intro a _
  exact (exponentialRace_eval w (u a)).measure_preimage (hs a).nullMeasurableSet

def DeletedMarkedSuccess {n r : ℕ} (u : Fin r → Fin n) (q : Fin r → ℕ)
    (c : Fin n → ℝ × ℝ) : Prop :=
  ∀ a, DeletedGapCount (Finset.univ.image u) (fun i => (c i).1) (q a) (c (u a)).2

lemma measurableSet_deletedMarkedSuccess {n r : ℕ} (u : Fin r → Fin n) (q : Fin r → ℕ) :
    MeasurableSet {c | DeletedMarkedSuccess u q c} := by
  simp only [DeletedMarkedSuccess, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  exact measurableSet_deletedGapCount (Finset.univ.image u)
    (fun (c : Fin n → ℝ × ℝ) i => (c i).1) (q a) (fun c => (c (u a)).2)
    (fun i => measurable_fst.comp (measurable_pi_apply i))
    (measurable_snd.comp (measurable_pi_apply (u a)))

/-- Tonelli uses the original independent clock family, with the unused
marked background coordinates integrated out. -/
theorem lintegral_deletedGapKernel_product {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (hu : Injective u) :
    (∫⁻ old, ∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a)
      ∂exponentialRace w) = pairedExponentialRace w {c | DeletedMarkedSuccess u q c} := by
  let A := {z : (Fin n → ℝ) × (Fin n → ℝ) |
    ∀ a, DeletedGapCount (Finset.univ.image u) z.1 (q a) (z.2 (u a))}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    exact measurableSet_deletedGapCount (Ω := (Fin n → ℝ) × (Fin n → ℝ))
      (Finset.univ.image u) Prod.fst (q a)
      (fun z => z.2 (u a)) (fun i => (measurable_pi_apply i).comp measurable_fst)
      ((measurable_pi_apply (u a)).comp measurable_snd)
  calc
    _ = ∫⁻ old, exponentialRace w ((Prod.mk old) ⁻¹' A) ∂exponentialRace w := by
      apply lintegral_congr
      intro old
      exact (deletedGapKernel_marked_product w old u q hu).symm
    _ = ((exponentialRace w).prod (exponentialRace w)) A := (Measure.prod_apply hA).symm
    _ = pairedExponentialRace w
        ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) ⁻¹' A) :=
      ((pairedExponentialRace_families w).measure_preimage hA.nullMeasurableSet).symm
    _ = _ := rfl

lemma swapped_deleted_count {n r : ℕ} (u : Fin r → Fin n)
    (c : Fin n → ℝ × ℝ) (t : ℝ) :
    deletedBeforeCount (Finset.univ.image u)
      (fun i => (swapClockCopies (Finset.univ.image u) c i).1) t =
      deletedBeforeCount (Finset.univ.image u) (fun i => (c i).1) t := by
  apply deletedBeforeCount_eq_of_eq_off
  intro i hi
  simp [swapClockCopies, hi]

/-- The exact event identity after resampling distinct marked labels. -/
theorem swapped_markedRankCylinder_iff_deleted_success {n r : ℕ}
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r → ℕ) (hq : StrictMono q) (hindex : ∀ a, q a + a.val = (j a).val)
    (c : Fin n → ℝ × ℝ)
    (hpos : ∀ i, 0 < (swapClockCopies (Finset.univ.image u) c i).1) :
    MarkedRankCylinder u j (fun i => (swapClockCopies (Finset.univ.image u) c i).1) ↔
      DeletedMarkedSuccess u q c := by
  rw [markedRankCylinder_iff_deleted_counts u j hu hj q hq hindex]
  have hmark (a : Fin r) : (swapClockCopies (Finset.univ.image u) c (u a)).1 = (c (u a)).2 := by
    simp [swapClockCopies]
  simp_rw [swapped_deleted_count, hmark]
  constructor
  · intro h a
    exact ⟨by simpa only [hmark a] using hpos (u a), h a⟩
  · intro h a
    exact (h a).2

/-- The paper's exact insertion identity for separated marked gaps. It
holds for the actual exponential race and actual deleted-gap masses. -/
theorem markedRankCylinder_probability_eq_deletedGapProduct {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r → ℕ) (hq : StrictMono q) (hindex : ∀ a, q a + a.val = (j a).val) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} =
      ∫⁻ old, ∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a)
        ∂exponentialRace w := by
  rw [lintegral_deletedGapKernel_product w u q hu]
  calc
    _ = pairedExponentialRace w {c | MarkedRankCylinder u j
        (fun i => (swapClockCopies (Finset.univ.image u) c i).1)} :=
      ((swapped_background_measurePreserving w (Finset.univ.image u)).measure_preimage
        (measurableSet_markedRankCylinder u j).nullMeasurableSet).symm
    _ = _ := by
      apply measure_congr
      filter_upwards [(swapped_background_measurePreserving w (Finset.univ.image u)).quasiMeasurePreserving.ae
        (exponentialRace_positive_background w)] with c hc
      exact propext (swapped_markedRankCylinder_iff_deleted_success u j hu hj q hq hindex c hc)

/-- Without separated gaps only inclusion is asserted: several marked
clocks may enter the same gap and still need the prescribed internal order.
Dropping that order gives the bound used for the weighted cylinder estimate. -/
theorem markedRankCylinder_probability_le_deletedGapProduct {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r → ℕ) (hindex : ∀ a, q a + a.val = (j a).val) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} ≤
      ∫⁻ old, ∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a)
        ∂exponentialRace w := by
  rw [lintegral_deletedGapKernel_product w u q hu]
  calc
    _ = pairedExponentialRace w {c | MarkedRankCylinder u j
        (fun i => (swapClockCopies (Finset.univ.image u) c i).1)} :=
      ((swapped_background_measurePreserving w (Finset.univ.image u)).measure_preimage
        (measurableSet_markedRankCylinder u j).nullMeasurableSet).symm
    _ ≤ _ := by
      apply measure_mono_ae
      filter_upwards [(swapped_background_measurePreserving w (Finset.univ.image u)).quasiMeasurePreserving.ae
        (exponentialRace_positive_background w)] with c hc
      intro hr a
      have hmark (a : Fin r) : (swapClockCopies (Finset.univ.image u) c (u a)).1 = (c (u a)).2 := by
        simp [swapClockCopies]
      refine ⟨by simpa only [hmark a] using hc (u a), ?_⟩
      have h := markedRankCylinder_deleted_counts u j hu hj _ hr a
      rw [swapped_deleted_count, hmark] at h
      have hi := hindex a
      change deletedBeforeCount (Finset.univ.image u) (fun i => (c i).1) (c (u a)).2 = q a
      omega

lemma deletedGapProduct_integrable {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n) (q : Fin r → ℕ) :
    Integrable (fun old => ∏ a, (deletedGapKernel w removed old (u a) (q a)).toReal)
      (exponentialRace w) := by
  have hm : Measurable (fun old => ∏ a, deletedGapKernel w removed old (u a) (q a)) :=
    Finset.measurable_prod _ (fun a _ => measurable_deletedGapKernel w removed (u a) (q a))
  have hle (old) : (∏ a, deletedGapKernel w removed old (u a) (q a)) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => zero_le) (fun a _ => deletedGapKernel_le_one w removed old (u a) (q a))
  have hi := integrable_toReal_of_lintegral_ne_top (μ := exponentialRace w) hm.aemeasurable
    (ne_of_lt ((lintegral_mono hle).trans_lt (by simp)))
  simpa only [ENNReal.toReal_prod] using hi

theorem markedRankCylinder_real_probability_eq_deletedGapProduct {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r → ℕ) (hq : StrictMono q) (hindex : ∀ a, q a + a.val = (j a).val) :
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} =
      ∫ old, ∏ a, (deletedGapKernel w (Finset.univ.image u) old (u a) (q a)).toReal
        ∂exponentialRace w := by
  have hm : Measurable (fun old => ∏ a,
      deletedGapKernel w (Finset.univ.image u) old (u a) (q a)) :=
    Finset.measurable_prod _ (fun a _ => measurable_deletedGapKernel w _ (u a) (q a))
  have hf : ∀ old, (∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a)) < ∞ := by
    intro old
    exact (Finset.prod_le_one (fun _ _ => zero_le)
      (fun a _ => deletedGapKernel_le_one w _ old (u a) (q a))).trans_lt (by simp)
  rw [Measure.real, markedRankCylinder_probability_eq_deletedGapProduct w u j hu hj q hq hindex,
    ← integral_toReal hm.aemeasurable (Filter.Eventually.of_forall hf)]
  simp only [ENNReal.toReal_prod]

end Luce
