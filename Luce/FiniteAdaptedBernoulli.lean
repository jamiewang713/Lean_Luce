import Luce.BernoulliProcess
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-! # Finite adapted zero-one rows

For `fixed_points.tex`, `lem:predictable-poisson`, a Boolean observation is
the equivalent finite-codomain encoding of an observation in `{0,1}`.
Only the filtration, observations, and their adaptation are input data.
Conditional probabilities are derived from conditional expectations and
clipped on null exceptional sets to give values in `[0,1]` everywhere.
The extension to a sequence is identically zero outside the finite row.
-/

open MeasureTheory Filter

namespace Luce

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A finite adapted zero-one row. The filtration index is shifted by one
because `Fin n` starts at zero: observation `k` is available at time `k+1`. -/
structure FiniteAdaptedBernoulli (P : Measure Ω) (n : ℕ) where
  filtration : Filtration ℕ mΩ
  observation : Fin n → Ω → Bool
  adapted : ∀ k, Measurable[filtration (k.val + 1)] (observation k)

namespace FiniteAdaptedBernoulli

variable {P : Measure Ω} {n : ℕ} (B : FiniteAdaptedBernoulli P n)

/-- The real-valued zero-one observation represented by the Boolean datum. -/
def observationReal (k : Fin n) (ω : Ω) : ℝ :=
  if B.observation k ω then 1 else 0

theorem observationReal_zero_one (k : Fin n) (ω : Ω) :
    B.observationReal k ω = 0 ∨ B.observationReal k ω = 1 := by
  simp only [observationReal]
  split_ifs <;> simp

theorem observationReal_nonneg (k : Fin n) (ω : Ω) :
    0 ≤ B.observationReal k ω := by
  rcases B.observationReal_zero_one k ω with h | h <;> simp [h]

theorem observationReal_le_one (k : Fin n) (ω : Ω) :
    B.observationReal k ω ≤ 1 := by
  rcases B.observationReal_zero_one k ω with h | h <;> simp [h]

theorem observationReal_adapted (k : Fin n) :
    StronglyMeasurable[B.filtration (k.val + 1)] (B.observationReal k) := by
  have h : Measurable (fun b : Bool => if b then (1 : ℝ) else 0) :=
    Measurable.of_discrete
  exact (h.comp (B.adapted k)).stronglyMeasurable

/-- A canonical everywhere-bounded version of the predictable conditional
probability. It agrees almost everywhere with the conditional expectation. -/
noncomputable def probability (k : Fin n) (ω : Ω) : ℝ :=
  max 0 (min 1 (P[B.observationReal k | B.filtration k.val] ω))

theorem probability_nonneg (k : Fin n) (ω : Ω) :
    0 ≤ B.probability k ω := le_max_left _ _

theorem probability_le_one (k : Fin n) (ω : Ω) :
    B.probability k ω ≤ 1 := max_le (by norm_num) (min_le_left _ _)

theorem probability_predictable (k : Fin n) :
    StronglyMeasurable[B.filtration k.val] (B.probability k) := by
  exact (measurable_const.max
    (measurable_const.min stronglyMeasurable_condExp.measurable)).stronglyMeasurable

variable [IsProbabilityMeasure P]

theorem integrable_observationReal (k : Fin n) : Integrable (B.observationReal k) P :=
  ⟨((B.observationReal_adapted k).mono (B.filtration.le (k.val + 1))).aestronglyMeasurable,
    HasFiniteIntegral.of_mem_Icc 0 1 (ae_of_all P (fun ω =>
      ⟨B.observationReal_nonneg k ω, B.observationReal_le_one k ω⟩))⟩

theorem integrable_probability (k : Fin n) : Integrable (B.probability k) P :=
  ⟨((B.probability_predictable k).mono (B.filtration.le k.val)).aestronglyMeasurable,
    HasFiniteIntegral.of_mem_Icc 0 1 (ae_of_all P (fun ω =>
      ⟨B.probability_nonneg k ω, B.probability_le_one k ω⟩))⟩

/-- Clipping changes only a null exceptional set, since a conditional
expectation of a zero-one observation lies in `[0,1]` almost everywhere. -/
theorem conditional_mean (k : Fin n) :
    P[B.observationReal k | B.filtration k.val] =ᵐ[P] B.probability k := by
  have hlo : 0 ≤ᵐ[P] P[B.observationReal k | B.filtration k.val] :=
    condExp_nonneg (ae_of_all P (B.observationReal_nonneg k))
  have hhi := condExp_mono (m := B.filtration k.val) (B.integrable_observationReal k)
    (integrable_const (1 : ℝ)) (ae_of_all P (B.observationReal_le_one k))
  rw [condExp_const (B.filtration.le k.val)] at hhi
  filter_upwards [hlo, hhi] with ω hωlo hωhi
  exact (max_eq_right hωlo).symm.trans (congrArg (max 0) (min_eq_right hωhi).symm)

theorem probability_ae_eq_condExp (k : Fin n) :
    B.probability k =ᵐ[P] P[B.observationReal k | B.filtration k.val] :=
  (B.conditional_mean k).symm

/-- Extend the finite row by zero observations and zero probabilities.
All analytic fields of `BernoulliProcess` follow from adaptation and the
conditional expectation; none is additional row data. -/
noncomputable def toProcess : BernoulliProcess P where
  filtration := B.filtration
  observation k := if hk : k < n then B.observationReal ⟨k, hk⟩ else 0
  probability k := if hk : k < n then B.probability ⟨k, hk⟩ else 0
  adapted k := by
    split_ifs with hk
    · exact B.observationReal_adapted ⟨k, hk⟩
    · exact stronglyMeasurable_zero
  predictable k := by
    split_ifs with hk
    · exact B.probability_predictable ⟨k, hk⟩
    · exact stronglyMeasurable_zero
  zero_one k ω := by
    split_ifs with hk
    · exact B.observationReal_zero_one ⟨k, hk⟩ ω
    · exact Or.inl rfl
  probability_nonneg k ω := by
    split_ifs with hk
    · exact B.probability_nonneg ⟨k, hk⟩ ω
    · exact le_rfl
  probability_le_one k ω := by
    split_ifs with hk
    · exact B.probability_le_one ⟨k, hk⟩ ω
    · norm_num
  conditional_mean k := by
    split_ifs with hk
    · exact B.conditional_mean ⟨k, hk⟩
    · rw [condExp_zero]

@[simp] theorem toProcess_filtration : B.toProcess.filtration = B.filtration := rfl

@[simp] theorem toProcess_observation (k : Fin n) :
    B.toProcess.observation k.val = B.observationReal k := by
  simp [toProcess, k.isLt]

@[simp] theorem toProcess_probability (k : Fin n) :
    B.toProcess.probability k.val = B.probability k := by
  simp [toProcess, k.isLt]

theorem toProcess_observation_of_le {k : ℕ} (hk : n ≤ k) :
    B.toProcess.observation k = 0 := by
  simp [toProcess, Nat.not_lt.mpr hk]

theorem toProcess_probability_of_le {k : ℕ} (hk : n ≤ k) :
    B.toProcess.probability k = 0 := by
  simp [toProcess, Nat.not_lt.mpr hk]

end FiniteAdaptedBernoulli
end Luce
