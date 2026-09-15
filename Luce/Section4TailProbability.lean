import Luce.Section4TailCount

/-! # Probability and integrability of the approved tail count

All measurability and integrability obligations here follow from the finite
count and the marginal laws; they are not additional model assumptions.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace Luce

lemma measurable_tailFixedPointCount {n : ℕ} (α : ℝ) :
    Measurable (fun e : Fin n → ℝ => tailFixedPointCount e α) := by
  classical
  simp only [tailFixedPointCount, Finset.card_filter]
  apply Finset.measurable_sum
  intro k _
  have hspatial : MeasurableSet {e : Fin n → ℝ | α * (n : ℝ) < (k.val : ℝ) + 1} := by
    by_cases h : α * (n : ℝ) < (k.val : ℝ) + 1 <;> simp [h]
  exact measurable_const.ite
    (hspatial.inter ((measurable_rankOf k) (measurableSet_singleton _)))
    measurable_const

lemma tailFixedPointCount_le {n : ℕ} (e : Fin n → ℝ) (α : ℝ) :
    tailFixedPointCount e α ≤ n := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

lemma integrable_tailFixedPointCount {n : ℕ} (w : Weights n) (α : ℝ) :
    Integrable (fun e => (tailFixedPointCount e α : ℝ)) (exponentialRace w) := by
  apply (integrable_const (n : ℝ)).mono'
    ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
      (measurable_tailFixedPointCount α)).aestronglyMeasurable
  exact Eventually.of_forall fun e => by
    simpa only [Function.comp_apply, Real.norm_natCast] using
      (Nat.cast_le (α := ℝ)).mpr (tailFixedPointCount_le e α)

lemma tailFixedPointCount_probability_le_expectation {n : ℕ} (w : Weights n) (α : ℝ) :
    (exponentialRace w).real {e | 0 < tailFixedPointCount e α} ≤
      ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace w := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun e => Nat.cast_nonneg (tailFixedPointCount e α))
    (integrable_tailFixedPointCount w α) (1 : ℝ)
  simpa only [one_mul, Nat.one_le_cast, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using h

lemma tailFixedPointCount_probability_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (w : Weights n) (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (E i) (expMeasure (w.rate i)) P)
    (hIndependent : iIndepFun E P) (α : ℝ) :
    P.real {ω | 0 < tailFixedPointCount (fun i => E i ω) α} =
      (exponentialRace w).real {e | 0 < tailFixedPointCount e α} := by
  have hJoint : HasLaw (fun ω i => E i ω) (exponentialRace w) P :=
    hIndependent.hasLaw_pi hLaw
  exact hJoint.measureReal_eq
    (measurableSet_lt measurable_const (measurable_tailFixedPointCount α))

end Luce
