import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Real

/-! # Total variation convergence of discrete probability laws

Source: `fixed_points.tex:958–961`. On a countable measurable space, convergence of
the individual probability masses to a probability law is uniform over all
events. We use the probability convention for total variation, the supremum
of the absolute difference of event probabilities.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

namespace Luce.CountableLaw
variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- Probability total variation: the supremum over events, with no factor two. -/
def probabilityTotalVariation (μ ν : ProbabilityMeasure E) : ℝ :=
  sSup (Set.range fun A : Set E => |(μ : Measure E).real A - (ν : Measure E).real A|)

private lemma probability_event_difference_le_one (μ ν : ProbabilityMeasure E)
    (A : Set E) : |(μ : Measure E).real A - (ν : Measure E).real A| ≤ 1 := by
  have hμ : (μ : Measure E).real A ≤ 1 := by
    simp
  have hν : (ν : Measure E).real A ≤ 1 := by
    simp
  have hμ0 : 0 ≤ (μ : Measure E).real A := measureReal_nonneg
  have hν0 : 0 ≤ (ν : Measure E).real A := measureReal_nonneg
  rw [abs_le]
  constructor <;> linarith


lemma probabilityTotalVariation_nonneg (μ ν : ProbabilityMeasure E) :
    0 ≤ probabilityTotalVariation μ ν := by
  have hb : BddAbove (Set.range fun A : Set E =>
      |(μ : Measure E).real A - (ν : Measure E).real A|) :=
    ⟨1, by rintro _ ⟨A, rfl⟩; exact probability_event_difference_le_one μ ν A⟩
  have h := le_csSup hb (Set.mem_range_self (∅ : Set E))
  simpa [probabilityTotalVariation] using h

lemma probabilityTotalVariation_le_one (μ ν : ProbabilityMeasure E) :
    probabilityTotalVariation μ ν ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨A, rfl⟩
  exact probability_event_difference_le_one μ ν A

lemma probability_event_difference_le_totalVariation (μ ν : ProbabilityMeasure E)
    (A : Set E) :
    |(μ : Measure E).real A - (ν : Measure E).real A| ≤ probabilityTotalVariation μ ν := by
  exact le_csSup ⟨1, by rintro _ ⟨B, rfl⟩; exact probability_event_difference_le_one μ ν B⟩
    (Set.mem_range_self A)

private lemma probability_finite_event_difference_le (μ ν : ProbabilityMeasure E)
    (s : Finset E) (A : Set E) :
    |(μ : Measure E).real (A ∩ (s : Set E)) -
      (ν : Measure E).real (A ∩ (s : Set E))| ≤
      ∑ k ∈ s, |(μ : Measure E).real {k} - (ν : Measure E).real {k}| := by
  classical
  have heq : A ∩ (s : Set E) = (s.filter (· ∈ A) : Set E) := by ext; simp [and_comm]
  rw [heq, ← sum_measureReal_singleton, ← sum_measureReal_singleton,
    ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => abs_nonneg _))

private lemma probability_event_le_finite_part_add_tail (μ : ProbabilityMeasure E)
    (s : Finset E) (A : Set E) :
    (μ : Measure E).real A ≤ (μ : Measure E).real (A ∩ (s : Set E)) +
      (μ : Measure E).real (s : Set E)ᶜ := by
  apply (measureReal_mono (show A ⊆ (A ∩ (s : Set E)) ∪ (s : Set E)ᶜ by
    intro x hx
    by_cases hs : x ∈ s
    · exact Or.inl ⟨hx, hs⟩
    · exact Or.inr hs) (measure_ne_top _ _)).trans
  exact measureReal_union_le _ _

/-- The finite-core estimate underlying the discrete Scheffé argument. -/
lemma probabilityTotalVariation_le_finite_sum (μ ν : ProbabilityMeasure E) (s : Finset E) :
    probabilityTotalVariation μ ν ≤
      2 * (∑ k ∈ s, |(μ : Measure E).real {k} - (ν : Measure E).real {k}|) +
      (ν : Measure E).real (s : Set E)ᶜ := by
  let e := ∑ k ∈ s, |(μ : Measure E).real {k} - (ν : Measure E).real {k}|
  have he : 0 ≤ e := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hfull : |(μ : Measure E).real s - (ν : Measure E).real s| ≤ e := by
    simpa only [univ_inter] using probability_finite_event_difference_le μ ν s univ
  have htail : (μ : Measure E).real (s : Set E)ᶜ ≤
      e + (ν : Measure E).real (s : Set E)ᶜ := by
    rw [probReal_compl_eq_one_sub s.measurableSet,
      probReal_compl_eq_one_sub s.measurableSet]
    have h := (abs_le.mp hfull).1
    linarith
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨A, rfl⟩
  have hfin := abs_le.mp (probability_finite_event_difference_le μ ν s A)
  have hμ := probability_event_le_finite_part_add_tail μ s A
  have hν := probability_event_le_finite_part_add_tail ν s A
  have hμm : (μ : Measure E).real (A ∩ (s : Set E)) ≤ (μ : Measure E).real A :=
    measureReal_mono inter_subset_left (measure_ne_top _ _)
  have hνm : (ν : Measure E).real (A ∩ (s : Set E)) ≤ (ν : Measure E).real A :=
    measureReal_mono inter_subset_left (measure_ne_top _ _)
  change |(μ : Measure E).real A - (ν : Measure E).real A| ≤
    2 * e + (ν : Measure E).real (s : Set E)ᶜ
  change -e ≤ _ ∧ _ ≤ e at hfin
  rw [abs_le]
  constructor <;> linarith

lemma probability_finite_tail_tendsto (ν : ProbabilityMeasure E) :
    Tendsto (fun s : Finset E => (ν : Measure E).real (s : Set E)ᶜ) atTop (𝓝 0) := by
  classical
  have hcover : (⋃ s : Finset E, (s : Set E)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨{x}, by simp⟩
  have h := tendsto_measure_iUnion_atTop (μ := (ν : Measure E))
    (s := fun s : Finset E => (s : Set E)) (fun _ _ h => h)
  rw [hcover] at h
  have h' : Tendsto (fun s : Finset E => (ν : Measure E).real (s : Set E)) atTop (𝓝 1) := by
    simpa only [Measure.real, Function.comp_def, measure_univ, ENNReal.toReal_one] using
      (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure E) univ)).comp h
  simpa only [probReal_compl_eq_one_sub (Finset.measurableSet _), sub_self] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub h'

/-- On a countable space, convergence of all point masses to a probability
law is uniform over all events. No tightness hypothesis is assumed. -/
theorem tendsto_probabilityTotalVariation_of_singletons
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (h : ∀ k, Tendsto (fun n => (μ n : Measure E).real {k}) atTop
      (𝓝 ((ν : Measure E).real {k}))) :
    Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (probabilityTotalVariation_nonneg _ _)
  · intro ε hε
    obtain ⟨s, hs⟩ := ((probability_finite_tail_tendsto ν).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε/2 by positivity))).exists
    have he : Tendsto (fun n => ∑ k ∈ s,
        |(μ n : Measure E).real {k} - (ν : Measure E).real {k}|) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum s
        (fun k _ => ((h k).sub (tendsto_const_nhds (x := (ν : Measure E).real {k}))).abs)
    filter_upwards [he.eventually (gt_mem_nhds (show (0 : ℝ) < ε/4 by positivity))] with n hn
    exact (probabilityTotalVariation_le_finite_sum (μ n) ν s).trans_lt (by linarith)

end Luce.CountableLaw


