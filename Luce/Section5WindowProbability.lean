import Luce.Section5Insertion
import Luce.Section5Resampling

/-!
# The probability comparison in the finite insertion argument

Source: `fixed_points.tex:1117–1136`. Threshold-count windows are the
order-statistic windows away from their finitely many endpoints. They are
used here to keep the counting, measurability, and law-preserving swap
explicit. The correspondence to the open time windows is a separate lemma.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

/-- Membership in the ghost window, expressed by the number of old clocks
strictly before the inserted time. The index `j` represents paper rank j+1. -/
def GhostCountWindow {n : ℕ} (ell : ℕ) (old : Fin n → ℝ)
    (j : Fin n) (t : ℝ) : Prop :=
  0 < t ∧ j.val + 1 ≤ clockBeforeCount old t + ell ∧
    clockBeforeCount old t < j.val + 1 + ell

lemma measurable_clockBeforeCount {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (c : Ω → Fin n → ℝ) (t : Ω → ℝ)
    (hc : ∀ i, Measurable (fun x => c x i)) (ht : Measurable t) :
    Measurable (fun x => clockBeforeCount (c x) (t x)) := by
  have heq : (fun x => clockBeforeCount (c x) (t x)) =
      (fun x => ∑ i : Fin n, if c x i < t x then (1 : ℕ) else 0) := by
    funext x
    simp [clockBeforeCount, Finset.sum_boole]
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt (hc i) ht) measurable_const measurable_const

lemma measurableSet_ghostCountWindow {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ell : ℕ) (c : Ω → Fin n → ℝ) (j : Fin n) (t : Ω → ℝ)
    (hc : ∀ i, Measurable (fun x => c x i)) (ht : Measurable t) :
    MeasurableSet {x | GhostCountWindow ell (c x) j (t x)} := by
  have hcount := measurable_clockBeforeCount c t hc ht
  exact (measurableSet_lt measurable_const ht).inter
    ((measurableSet_le measurable_const (hcount.add_const ell)).inter
      (measurableSet_lt hcount measurable_const))

/-- The endpoint `v` is appended, and need not be distinct from the sources. -/
def GhostCountSuccess {n m : ℕ} (ell : ℕ) (v : Fin n) (u : Fin m → Fin n)
    (c : Fin n → ℝ × ℝ) : Prop :=
  ∀ a, GhostCountWindow ell (fun i => (c i).1)
    ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) (c (u a)).2

def ApproximateClockPath {n m : ℕ} (q : ℕ) (v : Fin n) (u : Fin m → Fin n)
    (c : Fin n → ℝ) : Prop :=
  ∀ a, Nat.dist (clockBeforeCount c (c (u a)))
    ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ).val ≤ q

lemma measurableSet_ghostCountSuccess {n m : ℕ}
    (ell : ℕ) (v : Fin n) (u : Fin m → Fin n) :
    MeasurableSet {c | GhostCountSuccess ell v u c} := by
  simp only [GhostCountSuccess, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply measurableSet_ghostCountWindow
  · intro i; exact measurable_fst.comp (measurable_pi_apply i)
  · exact measurable_snd.comp (measurable_pi_apply (u a))

lemma measurableSet_approximateClockPath {n m : ℕ}
    (q : ℕ) (v : Fin n) (u : Fin m → Fin n) :
    MeasurableSet {c | ApproximateClockPath q v u c} := by
  simp only [ApproximateClockPath, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  have h := measurable_clockBeforeCount (fun c : Fin n → ℝ => c)
    (fun c => c (u a)) (fun i => measurable_pi_apply i) (measurable_pi_apply (u a))
  exact measurableSet_le
    ((show Measurable (fun k : ℕ => Nat.dist k
      ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ).val) from
        Measurable.of_discrete).comp h) measurable_const

/-- Deterministic implication after the actual finite set of coordinate
swaps. The cardinality bound holds also when sources repeat; distinctness
is needed later for the conditional product formula, not for this step. -/
theorem ghostCountSuccess_implies_swapped_path {n m : ℕ}
    (ell : ℕ) (v : Fin n) (u : Fin m → Fin n) (c : Fin n → ℝ × ℝ)
    (hsuccess : GhostCountSuccess ell v u c) :
    ApproximateClockPath (ell + m + 2) v u
      (fun i => (swapClockCopies (Finset.univ.image u) c i).1) := by
  intro a
  let s := Finset.univ.image u
  let old := fun i => (c i).1
  let new := fun i => (swapClockCopies s c i).1
  have hsame : ∀ i, i ∉ s → new i = old i := by
    intro i hi
    simp [new, old, swapClockCopies, hi]
  have hnew : new (u a) = (c (u a)).2 := by
    simp [new, s, swapClockCopies]
  have hdist := clockBeforeCount_dist_le_of_eq_off old new s hsame ((c (u a)).2)
  have hcard : s.card ≤ m := by
    simpa [s] using (Finset.card_image_le (s := Finset.univ) (f := u))
  have hwindow := hsuccess a
  rcases hwindow with ⟨_, hlo, hhi⟩
  change Nat.dist (clockBeforeCount new (new (u a))) _ ≤ _
  rw [hnew]
  dsimp [old] at hdist
  unfold Nat.dist at *
  omega

/-- Each success event is compared with the same approximate-path event
under the original background law. This is the measure-preserving
comparison at source lines 1121–1136, not an assumed coupling. -/
theorem ghostCountSuccess_probability_le {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) (u : Fin m → Fin n) :
    pairedExponentialRace w {c | GhostCountSuccess ell v u c} ≤
      exponentialRace w {c | ApproximateClockPath (ell + m + 2) v u c} := by
  calc
    _ ≤ pairedExponentialRace w
        {c | ApproximateClockPath (ell + m + 2) v u
          (fun i => (swapClockCopies (Finset.univ.image u) c i).1)} :=
      measure_mono (fun c hc => ghostCountSuccess_implies_swapped_path ell v u c hc)
    _ = _ := (swapped_background_measurePreserving w (Finset.univ.image u)).measure_preimage
      (measurableSet_approximateClockPath (ell + m + 2) v u).nullMeasurableSet

/-- Integrating a finite count is exactly the sum of its event probabilities;
this explicitly justifies the sum over all proposed source tuples. -/
lemma sum_measures_eq_lintegral_count {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (P : ι → Ω → Prop)
    (hP : ∀ i ∈ s, MeasurableSet {x | P i x}) :
    ∑ i ∈ s, μ {x | P i x} =
      ∫⁻ x, ((s.filter (fun i => P i x)).card : ℝ≥0∞) ∂μ := by
  calc
    _ = ∑ i ∈ s, ∫⁻ x, (if P i x then (1 : ℝ≥0∞) else 0) ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Set.indicator, Set.mem_ofPred_eq, one_mul] using
        (lintegral_indicator_const (hP i hi) (1 : ℝ≥0∞)).symm
    _ = ∫⁻ x, ∑ i ∈ s, (if P i x then (1 : ℝ≥0∞) else 0) ∂μ := by
      symm
      apply lintegral_finsetSum
      intro i hi
      exact Measurable.ite (hP i hi) measurable_const measurable_const
    _ = _ := by
      apply lintegral_congr
      intro x
      simp [Finset.sum_boole]

/-- The expected number of successful distinct-source insertions, uniformly
over all rates and all terminal vertices. This proves the probabilistic
swap-and-count step, including its source-distinctness restriction. -/
theorem sum_ghostCountSuccess_probability_le {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
      pairedExponentialRace w {c | GhostCountSuccess ell v u c} ≤
        ((2 * (ell + m + 2) + 1) ^ m : ℕ) := by
  let s := Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u)
  calc
    _ ≤ ∑ u ∈ s, exponentialRace w
        {c | ApproximateClockPath (ell + m + 2) v u c} := by
      exact Finset.sum_le_sum (fun u _ => ghostCountSuccess_probability_le w ell v u)
    _ = ∫⁻ c, ((s.filter (fun u => ApproximateClockPath (ell + m + 2) v u c)).card :
        ℝ≥0∞) ∂exponentialRace w :=
      sum_measures_eq_lintegral_count _ _ _
        (fun u _ => measurableSet_approximateClockPath _ v u)
    _ ≤ ∫⁻ _c, (((2 * (ell + m + 2) + 1) ^ m : ℕ) : ℝ≥0∞)
        ∂exponentialRace w := by
      apply lintegral_mono_ae
      filter_upwards [exponentialRace_injective_ae w] with c hc
      have heq : s.filter (fun u => ApproximateClockPath (ell + m + 2) v u c) =
          Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u ∧
            ApproximatePermutationPath (rankPermutation c hc) (ell + m + 2) v u) := by
        ext u
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      rw [heq]
      exact_mod_cast distinct_approximatePermutationPath_count_le
        (m := m) (rankPermutation c hc) (ell + m + 2) v
    _ = _ := by simp

/-- The conditional probability of inserting label i into rank-window j. -/
def ghostCountKernel {n : ℕ} (w : Weights n) (ell : ℕ) (old : Fin n → ℝ)
    (i j : Fin n) : ℝ≥0∞ :=
  expMeasure (w.rate i) {t | GhostCountWindow ell old j t}

lemma measurable_ghostCountKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (i j : Fin n) : Measurable (fun old => ghostCountKernel w ell old i j) := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  apply measurable_measure_prodMk_left (s :=
    {c : (Fin n → ℝ) × ℝ | GhostCountWindow ell c.1 j c.2})
  apply measurableSet_ghostCountWindow
  · intro k; exact (measurable_pi_apply k).comp measurable_fst
  · exact measurable_snd

/-- Distinct sources yield the product of their window probabilities.
Independence comes from the replacement race; windows share one background. -/
theorem ghostCountKernel_product {n m : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (v : Fin n) (u : Fin m → Fin n)
    (hu : Function.Injective u) :
    exponentialRace w {new | ∀ a, GhostCountWindow ell old
      ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) (new (u a))} =
        ∏ a, ghostCountKernel w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) := by
  let sets := fun a : Fin m => {t | GhostCountWindow ell old
    ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) t}
  have hs : ∀ a, MeasurableSet (sets a) := by
    intro a
    exact measurableSet_ghostCountWindow ell (fun _ => old) _ id
      (fun _ => measurable_const) measurable_id
  have h := ((exponentialRace_independent w).precomp hu).measure_inter_preimage_eq_mul
    Finset.univ (sets := sets) (fun a _ => hs a)
  simp only [Finset.mem_univ, iInter_true] at h
  have heq : (⋂ a, (fun new : Fin n → ℝ => new (u a)) ⁻¹' sets a) =
      {new | ∀ a, GhostCountWindow ell old
        ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) (new (u a))} := by
    ext new
    simp [sets]
  rw [← heq, h]
  apply Finset.prod_congr rfl
  intro a _
  exact (exponentialRace_eval w (u a)).measure_preimage (hs a).nullMeasurableSet

lemma measurableSet_ghostFamilySuccess {n m : ℕ}
    (ell : ℕ) (v : Fin n) (u : Fin m → Fin n) :
    MeasurableSet {c : (Fin n → ℝ) × (Fin n → ℝ) |
      ∀ a, GhostCountWindow ell c.1
        ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) (c.2 (u a))} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply measurableSet_ghostCountWindow
  · intro i; exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply (u a)).comp measurable_snd

/-- Tonelli and the actual independence of replacement clocks identify the
expectation of a window product with the successful-insertion probability. -/
theorem lintegral_ghostCountKernel_product {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) (u : Fin m → Fin n) (hu : Function.Injective u) :
    (∫⁻ old, ∏ a, ghostCountKernel w ell old (u a)
      ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) ∂exponentialRace w) =
      pairedExponentialRace w {c | GhostCountSuccess ell v u c} := by
  let A := {c : (Fin n → ℝ) × (Fin n → ℝ) |
      ∀ a, GhostCountWindow ell c.1
        ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) (c.2 (u a))}
  have hA : MeasurableSet A := measurableSet_ghostFamilySuccess ell v u
  calc
    _ = ∫⁻ old, exponentialRace w ((Prod.mk old) ⁻¹' A) ∂exponentialRace w := by
      apply lintegral_congr
      intro old
      exact (ghostCountKernel_product w ell old v u hu).symm
    _ = ((exponentialRace w).prod (exponentialRace w)) A :=
      (Measure.prod_apply hA).symm
    _ = pairedExponentialRace w
        ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) ⁻¹' A) :=
      ((pairedExponentialRace_families w).measure_preimage hA.nullMeasurableSet).symm
    _ = _ := rfl

/-- The full expected distinct-source path-product bound for count windows.
There is no additional hypothesis encoding the probability comparison.
Source: Lemma 5.3, `eq:finite-insertion-path`, with its explicit constant. -/
theorem finite_insertion_path_countWindow {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    (∫⁻ old,
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, ghostCountKernel w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
      ∂exponentialRace w) ≤ ((2 * (ell + m + 2) + 1) ^ m : ℕ) := by
  rw [lintegral_finsetSum]
  · have heq :
        (∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
          ∫⁻ old, ∏ a, ghostCountKernel w ell old (u a)
            ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) ∂exponentialRace w) =
        ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
          pairedExponentialRace w {c | GhostCountSuccess ell v u c} := by
      apply Finset.sum_congr rfl
      intro u hu
      exact lintegral_ghostCountKernel_product w ell v u (Finset.mem_filter.mp hu).2
    rw [heq]
    exact sum_ghostCountSuccess_probability_le w ell v
  · intro u _
    exact Finset.measurable_prod _ (fun _ _ => measurable_ghostCountKernel w ell _ _)

end Luce
