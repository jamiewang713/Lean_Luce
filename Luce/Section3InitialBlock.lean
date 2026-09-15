import Luce.Section3Mean
import Luce.Section3Profile

/-!
# Removing the initial labels

Source: `fixed_points.tex:761–763, 778–779, 795–797`.
The first few labels carry arbitrarily small normalized weight, uniformly
over sufficiently late rows, as a consequence of the actual L¹ assumption.
No bound on individual rates and no regularity at zero are assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- The paper's sum over all positive labels whose spatial coordinate is
at most the cutoff. Nonpositive cutoffs automatically select no labels. -/
def initialRateMass (w : WeightArray) (n : ℕ) (η : ℝ) : ℝ :=
  (∑ i : Fin (n + 1), if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ η
    then (w (n + 1)).rate i else 0) / (n + 1 : ℕ)

/-- Every selected label contributes precisely the mass of its entire cell;
the last fractional cell can only increase the upper bound on the right. -/
theorem initialRateMass_le_integral (w : WeightArray) (n : ℕ) (η : ℝ) :
    initialRateMass w n η ≤ ∫ x in Ioc (0 : ℝ) η, stepProfile w (n + 1) x ∂profileMeasure := by
  classical
  let s : Finset (Fin (n + 1)) := Finset.univ.filter
    (fun i => ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ η)
  let cell (i : Fin (n + 1)) := Ioc ((i.val : ℝ) / (n + 1 : ℕ))
    (((i.val : ℝ) + 1) / (n + 1 : ℕ))
  let term (i : Fin (n + 1)) : ℝ → ℝ :=
    (cell i).indicator (fun _ => (w (n + 1)).rate i)
  have hi (i : Fin (n + 1)) : Integrable (term i) profileMeasure :=
    (integrable_const _).indicator measurableSet_Ioc
  have heq : initialRateMass w n η = ∫ x, ∑ i ∈ s, term i x ∂profileMeasure := by
    rw [integral_finsetSum s (fun i _ => hi i)]
    simp_rw [term, cell, integral_indicator_const _ measurableSet_Ioc, smul_eq_mul,
      section3_cell_real_measure]
    simp [initialRateMass, s, Finset.sum_filter, div_eq_mul_inv, mul_comm,
      Finset.mul_sum, mul_ite]
  rw [heq, ← integral_indicator measurableSet_Ioc]
  apply integral_mono (integrable_finsetSum s (fun i _ => hi i))
    ((integrable_stepProfile w (n + 1)).indicator measurableSet_Ioc)
  intro x
  by_cases hx : x ∈ Ioc (0 : ℝ) η
  · rw [Set.indicator_of_mem hx]
    change _ ≤ ∑ i : Fin (n + 1),
      if (i.val : ℝ) / (n + 1 : ℕ) < x ∧ x ≤ ((i.val : ℝ) + 1) / (n + 1 : ℕ)
      then (w (n + 1)).rate i else 0
    have hterm (i : Fin (n + 1)) : term i x =
        if (i.val : ℝ) / (n + 1 : ℕ) < x ∧ x ≤ ((i.val : ℝ) + 1) / (n + 1 : ℕ)
        then (w (n + 1)).rate i else 0 := by simp [term, cell, Set.indicator_apply]
    simp_rw [← hterm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun i _ _ => Set.indicator_nonneg (fun _ _ => ((w (n + 1)).positive i).le) x)
  · rw [Set.indicator_of_notMem hx]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i his
    apply Set.indicator_of_notMem
    intro hxi
    apply hx
    exact ⟨(div_nonneg (Nat.cast_nonneg _) (by positivity)).trans_lt hxi.1,
      hxi.2.trans (Finset.mem_filter.mp his).2⟩

/-- Quantitative L¹ comparison for the initial label block. -/
theorem initialRateMass_le_limit_add_error {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (n : ℕ) (η : ℝ) :
    initialRateMass w n η ≤ (∫ x in Ioc (0 : ℝ) η, f x ∂profileMeasure) +
      ∫ x, |stepProfile w (n + 1) x - f x| ∂profileMeasure := by
  refine (initialRateMass_le_integral w n η).trans ?_
  have hbound : |(∫ x in Ioc (0 : ℝ) η, stepProfile w (n + 1) x ∂profileMeasure) -
      ∫ x in Ioc (0 : ℝ) η, f x ∂profileMeasure| ≤
      ∫ x, |stepProfile w (n + 1) x - f x| ∂profileMeasure := by
    rw [← integral_sub (integrable_stepProfile w (n + 1)).integrableOn hf.integrable.integrableOn]
    calc
      _ ≤ ∫ x in Ioc (0 : ℝ) η, |stepProfile w (n + 1) x - f x| ∂profileMeasure :=
        norm_integral_le_integral_norm (fun x => stepProfile w (n + 1) x - f x)
      _ ≤ _ := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun _ => abs_nonneg _)
        ((integrable_stepProfile w (n + 1)).sub hf.integrable).abs
  linarith [le_abs_self ((∫ x in Ioc (0 : ℝ) η, stepProfile w (n + 1) x ∂profileMeasure) -
    ∫ x in Ioc (0 : ℝ) η, f x ∂profileMeasure)]

/-- The double-limit initial-block estimate actually used in Section 3. -/
theorem ProfileLimit.initial_mass_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, initialRateMass w n η < ε := by
  have hmeasure : Tendsto (fun m : ℕ => profileMeasure (Ioc (0 : ℝ) (1 / (m + 1 : ℕ))))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun m : ℕ => ENNReal.ofReal (1 / (m + 1 : ℕ))) atTop (𝓝 0) from by
        simpa only [Nat.cast_add, Nat.cast_one, ENNReal.ofReal_zero] using
          ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      (fun _ => bot_le)
    intro m
    calc
      _ ≤ volume (Ioc (0 : ℝ) (1 / (m + 1 : ℕ))) := Measure.restrict_le_self _
      _ = _ := by rw [Real.volume_Ioc, sub_zero]
  have hbase := hf.integrable.tendsto_setIntegral_nhds_zero hmeasure
  obtain ⟨m, hm⟩ := (hbase.eventually (gt_mem_nhds (half_pos hε))).exists
  refine ⟨1 / (m + 1 : ℕ), by positivity, ?_⟩
  have herr := (hf.tendsto_integral_abs_sub.comp (tendsto_add_atTop_nat 1)).eventually
    (gt_mem_nhds (half_pos hε))
  filter_upwards [herr] with n hn
  dsimp only [Function.comp_def] at hn
  exact (initialRateMass_le_limit_add_error hf n _).trans_lt (by linarith)

end Luce
