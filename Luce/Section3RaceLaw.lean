import Luce.ExponentialMemoryless
import Luce.FirstChoice
import Luce.LuceMassRecursion
import Mathlib.Order.Fin.Tuple

/-!
# The exponential race and the full Luce permutation law

This proves the representation assertion preceding `eq:rank-representation`
from the independent exponential law, so the conditional probabilities of
Section 2 can be applied to the race used in Section 3. The target is the
exact permutation mass in `eq:luce-law`, including the empty permutation.
The statement and mechanism are recorded in `SECTION3_FORMALIZATION.md`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal

namespace Luce

/-- Product memorylessness: after every clock survives a deterministic time,
subtracting that time gives the original independent race, with its exact
unnormalized survival probability. No conditional law is assumed. -/
theorem exponentialRace_residual_measure {n : ℕ} (w : Weights n)
    {s : ℝ} (hs : 0 ≤ s) :
    ((exponentialRace w).restrict (Set.univ.pi (fun _ => Ioi s))).map
        (fun clocks i => clocks i - s) =
      ENNReal.ofReal (Real.exp (-(w.total Finset.univ * s))) • exponentialRace w := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  rw [exponentialRace, Measure.restrict_pi_pi]
  rw [Measure.pi_map_pi
    (μ := fun i : Fin n => (expMeasure (w.rate i)).restrict (Ioi s))
    (f := fun _ : Fin n => fun x : ℝ => x - s)
    (fun _ => (measurable_id.sub measurable_const).aemeasurable)]
  simp_rw [exponential_residual_measure (w.positive _) hs]
  have hprod : (∏ i, ENNReal.ofReal (Real.exp (-(w.rate i * s)))) =
      ENNReal.ofReal (Real.exp (-(w.total Finset.univ * s))) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
    rw [← Real.exp_sum]
    congr 2
    simp [Weights.total, Finset.sum_neg_distrib, Finset.sum_mul]
  letI : ∀ i : Fin n, IsFiniteMeasure
      (ENNReal.ofReal (Real.exp (-(w.rate i * s))) • expMeasure (w.rate i)) :=
    fun i => (expMeasure (w.rate i)).smul_finite ENNReal.ofReal_ne_top
  refine Measure.pi_eq
    (μ := fun i : Fin n => ENNReal.ofReal (Real.exp (-(w.rate i * s))) • expMeasure (w.rate i))
    (fun A hA => ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, hprod]

lemma measurableSet_strictMono_clocks (n : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ | StrictMono clocks} := by
  simp only [StrictMono, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  refine MeasurableSet.iInter fun _ => ?_
  exact measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

lemma strictMono_sub_const_iff {n : ℕ} (clocks : Fin n → ℝ) (s : ℝ) :
    StrictMono (fun i => clocks i - s) ↔ StrictMono clocks := by
  constructor <;> intro h i j hij
  · have hh := h hij
    linarith
  · exact sub_lt_sub_right (h hij) s

/-- The sorted event is invariant under subtracting a common time, while
the survival event contributes exactly the product exponential factor. -/
theorem exponentialRace_surviving_order {n : ℕ} (w : Weights n)
    {s : ℝ} (hs : 0 ≤ s) :
    exponentialRace w {clocks | (∀ i, s < clocks i) ∧ StrictMono clocks} =
      ENNReal.ofReal (Real.exp (-(w.total Finset.univ * s))) *
        exponentialRace w {clocks | StrictMono clocks} := by
  have hm := congrArg (fun ν : Measure (Fin n → ℝ) => ν {clocks | StrictMono clocks})
    (exponentialRace_residual_measure w hs)
  have hmap : Measurable (fun clocks : Fin n → ℝ => fun i => clocks i - s) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply i).sub measurable_const)
  rw [Measure.map_apply hmap (measurableSet_strictMono_clocks n),
    Measure.restrict_apply ((measurableSet_strictMono_clocks n).preimage hmap),
    Measure.smul_apply, smul_eq_mul] at hm
  convert hm using 1
  congr 1
  ext clocks
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_univ_pi, Set.mem_Ioi, strictMono_sub_const_iff]
  exact and_comm

/-- The distinguished-clock disintegration specialized to an arbitrary
measurable event; this is derived by integrating its indicator. -/
theorem exponentialRace_event_disintegrate {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (A : Set (ℝ × (Fin n → ℝ))) (hA : MeasurableSet A) :
    exponentialRace w {clocks | (clocks i, fun j => clocks (i.succAbove j)) ∈ A} =
      ∫⁻ t, exponentialPDF (w.rate i) t *
        backgroundRace w i {background | (t, background) ∈ A} := by
  classical
  have h := exponentialRace_disintegrate w i (A.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hA)
  have hclocks : Measurable (fun clocks : Fin (n + 1) → ℝ =>
      (clocks i, fun j => clocks (i.succAbove j))) :=
    (measurable_pi_apply i).prodMk (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
  have hleft := lintegral_indicator_fun_one (μ := exponentialRace w) (hA.preimage hclocks)
  have hright (t : ℝ) := lintegral_indicator_fun_one (μ := backgroundRace w i)
    (hA.preimage (measurable_const.prodMk measurable_id :
      Measurable (fun background : Fin n → ℝ => (t, background))))
  simp only [Set.indicator_apply, Set.mem_preimage] at h hleft hright
  rw [hleft] at h
  simpa only [hright, Set.preimage] using h

lemma backgroundRace_zero {n : ℕ} (w : Weights (n + 1)) :
    backgroundRace w 0 = exponentialRace (w.removeFirst 0) := by
  change (Measure.pi fun i : Fin n => expMeasure (w.rate ((0 : Fin (n + 1)).succAbove i))) =
    (Measure.pi fun i : Fin n => expMeasure (w.rate (Equiv.swap 0 0 i.succ)))
  simp only [Fin.succAbove_zero, Equiv.swap_self, Equiv.refl_apply]

lemma measurableSet_first_before_background (n : ℕ) :
    MeasurableSet {z : ℝ × (Fin n → ℝ) | ∀ j, z.1 < z.2 j} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt measurable_fst ((measurable_pi_apply j).comp measurable_snd)

lemma strictMono_clocks_iff {n : ℕ} (clocks : Fin (n + 1) → ℝ) :
    StrictMono clocks ↔
      (∀ j : Fin n, clocks 0 < clocks j.succ) ∧ StrictMono (fun j : Fin n => clocks j.succ) := by
  have heq : Fin.cons (clocks 0) (fun j : Fin n => clocks j.succ) = clocks := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [← heq, Fin.strictMono_cons]
  simp

/-- The first sorted clock can be exposed before all remaining clocks,
retaining their exact ordered-event probability. -/
theorem exponentialRace_order_disintegrate {n : ℕ} (w : Weights (n + 1)) :
    exponentialRace w {clocks | StrictMono clocks} =
      ∫⁻ t, exponentialPDF (w.rate 0) t *
        exponentialRace (w.removeFirst 0)
          {background | (∀ j, t < background j) ∧ StrictMono background} := by
  have hA := (measurableSet_first_before_background n).inter
    ((measurableSet_strictMono_clocks n).preimage measurable_snd)
  have h := exponentialRace_event_disintegrate w 0
    {z | (∀ j, z.1 < z.2 j) ∧ StrictMono z.2} hA
  simpa only [strictMono_clocks_iff, Fin.succAbove_zero, backgroundRace_zero, Set.mem_ofPred_eq] using h

lemma first_clock_event_iff {n : ℕ} (clocks : Fin (n + 1) → ℝ)
    (hinj : Function.Injective clocks) :
    (∀ j : Fin n, clocks 0 < clocks j.succ) ↔ raceRank clocks 0 = 1 := by
  classical
  have hzero : raceRank clocks 0 = 1 ↔ ∀ i : Fin (n + 1), ¬clocks i < clocks 0 := by
    simp [raceRank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rw [hzero]
  constructor
  · intro h i
    exact Fin.cases (lt_irrefl _) (fun j => not_lt.mpr (h j).le) i
  · intro h j
    have hle : clocks 0 ≤ clocks j.succ := le_of_not_gt (h j.succ)
    have hne : clocks 0 ≠ clocks j.succ := fun heq => Fin.succ_ne_zero j (hinj heq).symm
    exact lt_of_le_of_ne hle hne

/-- The unrestricted order of the background drops out of the first-choice
probability. This identity uses the already proved exact first-choice law. -/
theorem exponentialRace_first_clock_probability {n : ℕ} (w : Weights (n + 1)) :
    exponentialRace w {clocks | ∀ j : Fin n, clocks 0 < clocks j.succ} =
      ENNReal.ofReal (w.rate 0 / w.total Finset.univ) := by
  have heq : {clocks : Fin (n + 1) → ℝ | ∀ j : Fin n, clocks 0 < clocks j.succ} =ᵐ[exponentialRace w]
      {clocks | raceRank clocks 0 = 1} := by
    filter_upwards [exponentialRace_injective_ae w] with clocks hinj
    exact propext (first_clock_event_iff clocks hinj)
  rw [measure_congr heq, ← ofReal_measureReal, exponentialRace_first_choice]

/-- Exact probability that every independent clock survives a fixed time. -/
theorem exponentialRace_all_survive {n : ℕ} (w : Weights n) {s : ℝ} (hs : 0 ≤ s) :
    exponentialRace w {clocks | ∀ i, s < clocks i} =
      ENNReal.ofReal (Real.exp (-(w.total Finset.univ * s))) := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  have heq : {clocks : Fin n → ℝ | ∀ i, s < clocks i} = Set.univ.pi (fun _ => Ioi s) := by
    ext clocks
    simp
  rw [heq, exponentialRace, Measure.pi_pi]
  simp_rw [expMeasure_Ioi (w.positive _) hs]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  simp [Weights.total, Finset.sum_neg_distrib, Finset.sum_mul]

/-- The sorted-event probability satisfies exactly the same first-draw
recursion as the Luce mass. The factorization follows from product
memorylessness and integration, without assuming conditional independence. -/
theorem exponentialRace_order_recursion {n : ℕ} (w : Weights (n + 1)) :
    exponentialRace w {clocks | StrictMono clocks} =
      ENNReal.ofReal (w.rate 0 / w.total Finset.univ) *
        exponentialRace (w.removeFirst 0) {clocks | StrictMono clocks} := by
  let v : Weights n := w.removeFirst 0
  let K : ℝ≥0∞ := exponentialRace v {clocks | StrictMono clocks}
  have hfirst := exponentialRace_event_disintegrate w 0
    {z | ∀ j, z.1 < z.2 j} (measurableSet_first_before_background n)
  simp only [Set.mem_ofPred_eq, Fin.succAbove_zero, backgroundRace_zero] at hfirst
  have hint : (∫⁻ t, exponentialPDF (w.rate 0) t *
      exponentialRace v {background | ∀ j, t < background j}) =
        ENNReal.ofReal (w.rate 0 / w.total Finset.univ) := by
    rw [← hfirst]
    exact exponentialRace_first_clock_probability w
  rw [exponentialRace_order_disintegrate]
  calc
    _ = ∫⁻ t, (exponentialPDF (w.rate 0) t *
        exponentialRace v {background | ∀ j, t < background j}) * K := by
      apply lintegral_congr
      intro t
      by_cases ht : 0 ≤ t
      · rw [exponentialRace_surviving_order v ht, exponentialRace_all_survive v ht]
        exact mul_assoc _ _ _ |>.symm
      · simp [exponentialPDF_of_neg (lt_of_not_ge ht)]
    _ = (∫⁻ t, exponentialPDF (w.rate 0) t *
        exponentialRace v {background | ∀ j, t < background j}) * K :=
      lintegral_mul_const' K _ (measure_ne_top _ _)
    _ = _ := by rw [hint]

/-- The increasing-label order has exactly its Luce product mass, by the
first-clock recursion. The induction begins with the genuinely empty race. -/
theorem exponentialRace_identity_order_probability {n : ℕ} (w : Weights n) :
    exponentialRace w {clocks | StrictMono clocks} =
      ENNReal.ofReal (w.mass (Equiv.refl (Fin n))) := by
  induction n with
  | zero =>
    have heq : {clocks : Fin 0 → ℝ | StrictMono clocks} = Set.univ := by
      ext clocks
      simp [StrictMono]
    simp [heq, Weights.mass]
  | succ n ih =>
    rw [exponentialRace_order_recursion, ih]
    rw [← ENNReal.ofReal_mul (div_nonneg (w.positive 0).le (w.total_nonneg _))]
    congr 1
    have hid : Equiv.Perm.decomposeFin.symm (0, Equiv.refl (Fin n)) =
        Equiv.refl (Fin (n + 1)) := by
      apply Equiv.ext
      intro i
      exact Fin.cases (by simp) (fun j => by simp) i
    simpa only [hid] using (Weights.mass_decomposeFin w 0 (Equiv.refl (Fin n))).symm

/-- The complete exponential-race representation of `eq:luce-law`.
The event records the entire draw order, rather than merely its first draw.
No normalization is needed because the Luce law is invariant under scaling. -/
theorem exponentialRace_order_probability {n : ℕ} (w : Weights n)
    (π : Equiv.Perm (Fin n)) :
    (exponentialRace w).real {clocks | StrictMono (fun r => clocks (π r))} =
      w.mass π := by
  let v : Weights n := ⟨fun i => w.rate (π i), fun i => w.positive (π i)⟩
  letI : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) π
  have he : MeasurePreserving e (exponentialRace v) (exponentialRace w) :=
    measurePreserving_piCongrLeft (fun i => expMeasure (w.rate i)) π
  have hpre := (MeasurePreserving.symm e he).measure_preimage
    (measurableSet_strictMono_clocks n).nullMeasurableSet
  have hmass : v.mass (Equiv.refl (Fin n)) = w.mass π := rfl
  have hmeasure : exponentialRace w {clocks | StrictMono (fun r => clocks (π r))} =
      ENNReal.ofReal (w.mass π) := by
    calc
      _ = exponentialRace v {clocks | StrictMono clocks} := hpre
      _ = _ := by rw [exponentialRace_identity_order_probability, hmass]
  rw [Measure.real, hmeasure, ENNReal.toReal_ofReal (w.mass_pos π).le]

end Luce
