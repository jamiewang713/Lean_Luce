import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Real

/-! # Total variation convergence of discrete probability laws

Source: `fixed_points.tex:958–961`. On the natural numbers, convergence of
the individual probability masses to a probability law is uniform over all
events. We use the probability convention for total variation, the supremum
of the absolute difference of event probabilities.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

namespace Luce

/-- Probability total variation: the supremum over events, with no factor two. -/
def probabilityTotalVariation (μ ν : ProbabilityMeasure ℕ) : ℝ :=
  sSup (Set.range fun A : Set ℕ => |(μ : Measure ℕ).real A - (ν : Measure ℕ).real A|)

private lemma probability_event_difference_le_one (μ ν : ProbabilityMeasure ℕ)
    (A : Set ℕ) : |(μ : Measure ℕ).real A - (ν : Measure ℕ).real A| ≤ 1 := by
  have hμ : (μ : Measure ℕ).real A ≤ 1 := by
    simp
  have hν : (ν : Measure ℕ).real A ≤ 1 := by
    simp
  have hμ0 : 0 ≤ (μ : Measure ℕ).real A := measureReal_nonneg
  have hν0 : 0 ≤ (ν : Measure ℕ).real A := measureReal_nonneg
  rw [abs_le]
  constructor <;> linarith

lemma probabilityTotalVariation_nonneg (μ ν : ProbabilityMeasure ℕ) :
    0 ≤ probabilityTotalVariation μ ν := by
  have hb : BddAbove (Set.range fun A : Set ℕ =>
      |(μ : Measure ℕ).real A - (ν : Measure ℕ).real A|) :=
    ⟨1, by rintro _ ⟨A, rfl⟩; exact probability_event_difference_le_one μ ν A⟩
  have h := le_csSup hb (Set.mem_range_self (∅ : Set ℕ))
  simpa [probabilityTotalVariation] using h

lemma probabilityTotalVariation_le_one (μ ν : ProbabilityMeasure ℕ) :
    probabilityTotalVariation μ ν ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨A, rfl⟩
  exact probability_event_difference_le_one μ ν A

lemma probability_event_difference_le_totalVariation (μ ν : ProbabilityMeasure ℕ)
    (A : Set ℕ) :
    |(μ : Measure ℕ).real A - (ν : Measure ℕ).real A| ≤ probabilityTotalVariation μ ν := by
  exact le_csSup ⟨1, by rintro _ ⟨B, rfl⟩; exact probability_event_difference_le_one μ ν B⟩
    (Set.mem_range_self A)

private lemma probability_finite_event_difference_le (μ ν : ProbabilityMeasure ℕ)
    (s : Finset ℕ) (A : Set ℕ) :
    |(μ : Measure ℕ).real (A ∩ (s : Set ℕ)) -
      (ν : Measure ℕ).real (A ∩ (s : Set ℕ))| ≤
      ∑ k ∈ s, |(μ : Measure ℕ).real {k} - (ν : Measure ℕ).real {k}| := by
  classical
  have heq : A ∩ (s : Set ℕ) = (s.filter (· ∈ A) : Set ℕ) := by ext; simp [and_comm]
  rw [heq, ← sum_measureReal_singleton, ← sum_measureReal_singleton,
    ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => abs_nonneg _))

private lemma probability_event_le_finite_part_add_tail (μ : ProbabilityMeasure ℕ)
    (s : Finset ℕ) (A : Set ℕ) :
    (μ : Measure ℕ).real A ≤ (μ : Measure ℕ).real (A ∩ (s : Set ℕ)) +
      (μ : Measure ℕ).real (s : Set ℕ)ᶜ := by
  apply (measureReal_mono (show A ⊆ (A ∩ (s : Set ℕ)) ∪ (s : Set ℕ)ᶜ by
    intro x hx
    by_cases hs : x ∈ s
    · exact Or.inl ⟨hx, hs⟩
    · exact Or.inr hs) (measure_ne_top _ _)).trans
  exact measureReal_union_le _ _

/-- The finite-core estimate underlying the discrete Scheffé argument. -/
lemma probabilityTotalVariation_le_finite_sum (μ ν : ProbabilityMeasure ℕ) (s : Finset ℕ) :
    probabilityTotalVariation μ ν ≤
      2 * (∑ k ∈ s, |(μ : Measure ℕ).real {k} - (ν : Measure ℕ).real {k}|) +
      (ν : Measure ℕ).real (s : Set ℕ)ᶜ := by
  let e := ∑ k ∈ s, |(μ : Measure ℕ).real {k} - (ν : Measure ℕ).real {k}|
  have he : 0 ≤ e := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hfull : |(μ : Measure ℕ).real s - (ν : Measure ℕ).real s| ≤ e := by
    simpa only [univ_inter] using probability_finite_event_difference_le μ ν s univ
  have htail : (μ : Measure ℕ).real (s : Set ℕ)ᶜ ≤
      e + (ν : Measure ℕ).real (s : Set ℕ)ᶜ := by
    rw [probReal_compl_eq_one_sub s.measurableSet,
      probReal_compl_eq_one_sub s.measurableSet]
    have h := (abs_le.mp hfull).1
    linarith
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨A, rfl⟩
  have hfin := abs_le.mp (probability_finite_event_difference_le μ ν s A)
  have hμ := probability_event_le_finite_part_add_tail μ s A
  have hν := probability_event_le_finite_part_add_tail ν s A
  have hμm : (μ : Measure ℕ).real (A ∩ (s : Set ℕ)) ≤ (μ : Measure ℕ).real A :=
    measureReal_mono inter_subset_left (measure_ne_top _ _)
  have hνm : (ν : Measure ℕ).real (A ∩ (s : Set ℕ)) ≤ (ν : Measure ℕ).real A :=
    measureReal_mono inter_subset_left (measure_ne_top _ _)
  change |(μ : Measure ℕ).real A - (ν : Measure ℕ).real A| ≤
    2 * e + (ν : Measure ℕ).real (s : Set ℕ)ᶜ
  change -e ≤ _ ∧ _ ≤ e at hfin
  rw [abs_le]
  constructor <;> linarith

private lemma probability_nat_tail_tendsto (ν : ProbabilityMeasure ℕ) :
    Tendsto (fun N : ℕ => (ν : Measure ℕ).real (Finset.Iic N : Set ℕ)ᶜ) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ℕ) univ)).comp
    (tendsto_measure_Iic_atTop (ν : Measure ℕ))
  have h' : Tendsto (fun N : ℕ => (ν : Measure ℕ).real (Finset.Iic N : Set ℕ))
      atTop (𝓝 1) := by
    simpa only [Finset.coe_Iic, Measure.real, measure_univ, ENNReal.toReal_one,
      Function.comp_def] using h
  simpa only [probReal_compl_eq_one_sub (Finset.Iic _).measurableSet, sub_self]
    using (tendsto_const_nhds (x := (1 : ℝ))).sub h'

/-- Source: `fixed_points.tex:958–961`. Pointwise convergence of the masses to
a probability law implies convergence in probability total variation. -/
theorem tendsto_probabilityTotalVariation_of_singletons
    {μ : ℕ → ProbabilityMeasure ℕ} {ν : ProbabilityMeasure ℕ}
    (h : ∀ k, Tendsto (fun n => (μ n : Measure ℕ).real {k}) atTop
      (𝓝 ((ν : Measure ℕ).real {k}))) :
    Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n => ha.trans_le (probabilityTotalVariation_nonneg _ _)
  · intro ε hε
    obtain ⟨N, hN⟩ := ((probability_nat_tail_tendsto ν).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))).exists
    have he : Tendsto (fun n => ∑ k ∈ Finset.Iic N,
        |(μ n : Measure ℕ).real {k} - (ν : Measure ℕ).real {k}|) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.Iic N)
        (fun k _ => ((h k).sub
          (tendsto_const_nhds (x := (ν : Measure ℕ).real {k}))).abs)
    filter_upwards [he.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))] with n hn
    exact (probabilityTotalVariation_le_finite_sum (μ n) ν (Finset.Iic N)).trans_lt (by linarith)

/-- Source: `fixed_points.tex:958–961`. Weak convergence on the discrete count
space implies the required singleton-probability convergence. -/
theorem tendsto_probability_singletons_of_weak
    {μ : ℕ → ProbabilityMeasure ℕ} {ν : ProbabilityMeasure ℕ}
    (h : Tendsto μ atTop (𝓝 ν)) (k : ℕ) :
    Tendsto (fun n => (μ n : Measure ℕ).real {k}) atTop
      (𝓝 ((ν : Measure ℕ).real {k})) := by
  have hk := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h
    (isClopen_discrete ({k} : Set ℕ))
  simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
    NNReal.continuous_coe.continuousAt.tendsto.comp hk

/-- Weak convergence to a proper natural-number law upgrades to total variation. -/
theorem tendsto_probabilityTotalVariation_of_weak
    {μ : ℕ → ProbabilityMeasure ℕ} {ν : ProbabilityMeasure ℕ}
    (h : Tendsto μ atTop (𝓝 ν)) :
    Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0) :=
  tendsto_probabilityTotalVariation_of_singletons (tendsto_probability_singletons_of_weak h)

/-- The same upgrade, directly in the bounded continuous test formulation of
weak convergence used for the point-process limit. -/
theorem tendsto_probabilityTotalVariation_of_integrals
    {μ : ℕ → ProbabilityMeasure ℕ} {ν : ProbabilityMeasure ℕ}
    (h : ∀ F : ℕ →ᵇ ℝ, Tendsto
      (fun n => ∫ k, F k ∂(μ n : Measure ℕ)) atTop
      (𝓝 (∫ k, F k ∂(ν : Measure ℕ)))) :
    Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0) :=
  tendsto_probabilityTotalVariation_of_weak
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr h)

end Luce
