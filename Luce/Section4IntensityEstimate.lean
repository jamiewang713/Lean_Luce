import Luce.Section4Compensator
import Luce.Section4Count

/-! # Terminal intensity tests bounded by actual endpoint expectations

Source: `fixed_points.tex:936–950`. The boundedness premise of the abstract
expectation lemma is discharged here from the manuscript assumptions.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace Luce

lemma integrable_interior_observed_test {n : ℕ} (w : Weights n) (β : ℝ)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    Integrable (fun e => ∫ y, g y ∂((interiorFixedPoints β (raceDraw e)).toFiniteMeasure :
      Measure (Icc (0 : ℝ) 1))) (exponentialRace w) := by
  let B := raceInteriorBernoulli w β
  have heq (e : Fin n → ℝ) :
      (∫ y, g y ∂((interiorFixedPoints β (raceDraw e)).toFiniteMeasure :
        Measure (Icc (0 : ℝ) 1))) =
        ∑ k, B.observationReal k e * g (section3Location n k) := by
    rw [← raceInteriorBernoulli_pointMeasure w β e]
    exact integral_observedPointMeasure _ _ _ g.continuous.measurable
  simp_rw [heq]
  exact integrable_finsetSum _ (fun k _ => (B.integrable_observationReal k).mul_const _)

/-- A continuous test in [0,1], zero before α, counts no more than the actual
terminal fixed points. This holds for every interior cutoff β. -/
lemma interior_observed_test_le_tail {n : ℕ} (e : Fin n → ℝ)
    (hinj : Function.Injective e) (α β : ℝ) (g : Icc (0 : ℝ) 1 →ᵇ ℝ)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hsupport : ∀ x, x.val ≤ α → g x = 0) :
    (∫ y, g y ∂((interiorFixedPoints β (raceDraw e)).toFiniteMeasure :
      Measure (Icc (0 : ℝ) 1))) ≤ (tailFixedPointCount e α : ℝ) := by
  classical
  rw [interiorFixedPoints, integral_observedPointMeasure _ _ _ g.continuous.measurable]
  simp only [tailFixedPointCount, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro k _
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
  have hfix := raceDraw_fixed_iff_rankOf e hinj k
  have hspace : α < (section3Location n k).val ↔ α * n < (k.val : ℝ) + 1 :=
    lt_div_iff₀ hn
  by_cases htail : α * n < (k.val : ℝ) + 1 ∧ rankOf e k = k.val + 1
  · simp only [htail, true_and, if_true, Nat.cast_one, decide_eq_true_eq]
    split_ifs
    · simpa using (hg (section3Location n k)).2
    · norm_num
  · have hz : (if decide (((k.val : ℝ) + 1) / n ≤ β ∧ (raceDraw e).symm k = k)
        then (1 : ℝ) else 0) * g (section3Location n k) = 0 := by
      by_cases hfixed : (raceDraw e).symm k = k
      · have hle : (section3Location n k).val ≤ α :=
          le_of_not_gt (fun h => htail ⟨hspace.mp h, hfix.mp hfixed⟩)
        rw [hsupport _ hle, mul_zero]
      · simp [hfixed]
    simp only [htail, if_false, Nat.cast_zero, hz, le_refl]

lemma integral_interior_observed_test_le_tail {n : ℕ} (w : Weights n)
    (α β : ℝ) (g : Icc (0 : ℝ) 1 →ᵇ ℝ)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hsupport : ∀ x, x.val ≤ α → g x = 0) :
    (∫ e, ∫ y, g y ∂((interiorFixedPoints β (raceDraw e)).toFiniteMeasure :
      Measure (Icc (0 : ℝ) 1)) ∂exponentialRace w) ≤
      ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace w := by
  apply integral_mono_ae (integrable_interior_observed_test w β g)
    (integrable_tailFixedPointCount w α)
  filter_upwards [exponentialRace_injective_ae w] with e he
  exact interior_observed_test_le_tail e he α β g hg hsupport

/-- The central endpoint intensity estimate for every nonnegative continuous
test bounded by one and supported in the tail. All bounds and convergence
hypotheses have been discharged from the paper's normalization, profile and
endpoint assumptions. The estimate is uniform in the interior cutoff β. -/
theorem section4_intensity_test_bound
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ → ∀ β : ℝ, ∀ hβ : β < 1,
      ∀ g : Icc (0 : ℝ) 1 →ᵇ ℝ,
        (∀ x, 0 ≤ g x ∧ g x ≤ 1) → (∀ x, x.val ≤ 1 - ε → g x = 0) →
        (∫ y, g y ∂(interiorIntensity w f hf β hβ : Measure (Icc (0 : ℝ) 1))) ≤
          (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4) := by
  obtain ⟨γ, hγ, δ, hδ, hest⟩ := endpointAssumption_epsilon_estimate_bounded w hnorm hend
  refine ⟨γ, hγ, min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro ε hε hεδ β hβ g hg hsupport
  obtain ⟨hb, hpower⟩ := hest ε hε (hεδ.trans_le (min_le_left _ _))
  let A := fun n => ∫ e, ∫ y, g y
    ∂((interiorFixedPoints β (raceDraw e)).toFiniteMeasure : Measure (Icc (0 : ℝ) 1))
    ∂exponentialRace (w n)
  have hcomp (n : ℕ) : A (n + 1) ≤ epsilonTailExpectation (fun n => w (n + 1)) ε n := by
    have h := integral_interior_observed_test_le_tail (w (n + 1)) (1 - ε) β g hg hsupport
    simpa only [tailFixedPointCount_eq_terminalFixedPointCount n _ hε
      (hεδ.trans_le (min_le_right _ _)), epsilonTailExpectation] using h
  have hAb : IsBoundedUnder (· ≤ ·) atTop A := by
    obtain ⟨C, hC⟩ := hb
    obtain ⟨N, hN⟩ := eventually_atTop.mp hC
    refine ⟨C, eventually_atTop.mpr ⟨N + 1, ?_⟩⟩
    intro n hn
    cases n with
    | zero => omega
    | succ n => exact (hcomp n).trans (hN n (by omega))
  have hlo := section4_interior_test_expectation_lower w f hnorm hf hβ g
    (fun x => (hg x).1) hAb
  have hupper := limsup_le_limsup (Eventually.of_forall hcomp)
    (isCoboundedUnder_le_of_le atTop (fun n =>
      integral_nonneg (fun e => integral_nonneg (fun y => (hg y).1)))) hb
  rw [limsup_nat_add A 1] at hupper
  exact hlo.trans (hupper.trans hpower)

end Luce
