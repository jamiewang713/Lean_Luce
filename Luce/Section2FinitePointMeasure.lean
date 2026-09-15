import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Function.Floor

/-! # Actual finite point measures on a measurable topological space

For `fixed_points.tex`, `lem:predictable-poisson`. A finite point measure is
an actual finite measure which is a finite sum of unit Dirac measures.
It carries the evaluation sigma algebra and the induced weak topology.
No separation, metrizability, or nonemptiness assumption is imposed.
-/

open MeasureTheory
open scoped BigOperators Topology NNReal

namespace Luce

variable {X : Type*} [MeasurableSpace X]

/-- The actual finite measure associated with a finite family of points. -/
noncomputable def pointMeasureOfFin {m : ℕ} (x : Fin m → X) : FiniteMeasure X :=
  ∑ i, (diracProba (x i)).toFiniteMeasure

private theorem finiteMeasure_mass_add (μ ν : FiniteMeasure X) :
    (μ + ν).mass = μ.mass + ν.mass := by
  simp [FiniteMeasure.mass, FiniteMeasure.coeFn_add]

private theorem finiteMeasure_mass_sum {ι : Type*} (s : Finset ι)
    (μ : ι → FiniteMeasure X) :
    (∑ i ∈ s, μ i).mass = ∑ i ∈ s, (μ i).mass := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, finiteMeasure_mass_add, ih]

@[simp] theorem pointMeasureOfFin_mass {m : ℕ} (x : Fin m → X) :
    (pointMeasureOfFin x).mass = m := by
  simp [pointMeasureOfFin, finiteMeasure_mass_sum]

/-- Finite point measures, represented as measures rather than labeled lists. -/
def FinitePointMeasure (X : Type*) [MeasurableSpace X] :=
  {μ : FiniteMeasure X // ∃ (m : ℕ) (x : Fin m → X), pointMeasureOfFin x = μ}

namespace FinitePointMeasure

instance : MeasurableSpace (FinitePointMeasure X) :=
  inferInstanceAs (MeasurableSpace {μ : FiniteMeasure X //
    ∃ (m : ℕ) (x : Fin m → X), pointMeasureOfFin x = μ})

/-- Forget only the proof of finite counting-measure representability. -/
def toFiniteMeasure (μ : FinitePointMeasure X) : FiniteMeasure X := μ.val

instance : Coe (FinitePointMeasure X) (FiniteMeasure X) := ⟨toFiniteMeasure⟩

/-- The measure represented by a finite family; repeated points are retained. -/
noncomputable def ofFin {m : ℕ} (x : Fin m → X) : FinitePointMeasure X :=
  ⟨pointMeasureOfFin x, m, x, rfl⟩

instance : Zero (FinitePointMeasure X) :=
  ⟨⟨0, 0, Fin.elim0, by simp [pointMeasureOfFin]⟩⟩

@[simp] theorem toFiniteMeasure_ofFin {m : ℕ} (x : Fin m → X) :
    (ofFin x).toFiniteMeasure = pointMeasureOfFin x := rfl

@[simp] theorem toFiniteMeasure_zero :
    (0 : FinitePointMeasure X).toFiniteMeasure = 0 := rfl

/-- Counts on a measurable set; the finite Dirac representation makes this
an actual natural-number count. -/
noncomputable def count (μ : FinitePointMeasure X) (B : Set X) : ℕ :=
  Nat.floor (μ.toFiniteMeasure B : ℝ)

@[simp] theorem ofFin_mass {m : ℕ} (x : Fin m → X) :
    (ofFin x).toFiniteMeasure.mass = m := pointMeasureOfFin_mass x

theorem measurable_toFiniteMeasure :
    Measurable (toFiniteMeasure : FinitePointMeasure X → FiniteMeasure X) :=
  measurable_subtype_coe

theorem measurable_toMeasure :
    Measurable (fun μ : FinitePointMeasure X => (μ.toFiniteMeasure : Measure X)) :=
  measurable_subtype_coe.comp measurable_toFiniteMeasure

theorem measurable_count {B : Set X} (hB : MeasurableSet B) :
    Measurable (fun μ : FinitePointMeasure X => μ.count B) := by
  exact Nat.measurable_floor.comp
    (((Measure.measurable_coe hB).comp measurable_toMeasure).ennreal_toReal)

theorem measurable_ofFin {m : ℕ} :
    Measurable (ofFin : (Fin m → X) → FinitePointMeasure X) := by
  apply Measurable.subtype_mk
  apply Measurable.subtype_mk
  change Measurable (fun x : Fin m → X => (pointMeasureOfFin x : Measure X))
  simp only [pointMeasureOfFin, FiniteMeasure.toMeasure_sum, diracProba]
  exact Finset.measurable_sum _ (fun i _ =>
    Measure.measurable_dirac.comp (measurable_pi_apply i))

section Topology

variable [TopologicalSpace X] [OpensMeasurableSpace X]

instance : TopologicalSpace (FinitePointMeasure X) :=
  inferInstanceAs (TopologicalSpace {μ : FiniteMeasure X //
    ∃ (m : ℕ) (x : Fin m → X), pointMeasureOfFin x = μ})

theorem continuous_toFiniteMeasure :
    Continuous (toFiniteMeasure : FinitePointMeasure X → FiniteMeasure X) :=
  continuous_subtype_val

theorem continuous_ofFin {m : ℕ} :
    Continuous (ofFin : (Fin m → X) → FinitePointMeasure X) := by
  apply Continuous.subtype_mk
  apply continuous_finsetSum
  intro i _
  exact ProbabilityMeasure.toFiniteMeasure_continuous.comp
    (continuous_diracProba.comp (continuous_apply i))

/-- The finite count bound is compact for literal open-cover compactness;
no Hausdorff condition on the original spatial space is needed. -/
theorem isCompact_mass_le [CompactSpace X] (N : ℕ) :
    IsCompact {μ : FinitePointMeasure X | μ.toFiniteMeasure.mass ≤ N} := by
  have hset : {μ : FinitePointMeasure X | μ.toFiniteMeasure.mass ≤ N} =
      ⋃ m ∈ Finset.range (N + 1), Set.range (ofFin (X := X) (m := m)) := by
    ext μ
    constructor
    · intro hμ
      obtain ⟨m, x, hx⟩ := μ.property
      have hm : m ≤ N := by
        have heq : μ.toFiniteMeasure.mass = m := by
          change μ.val.mass = m
          rw [← hx]
          exact pointMeasureOfFin_mass x
        change μ.toFiniteMeasure.mass ≤ (N : ℝ≥0) at hμ
        rw [heq] at hμ
        exact_mod_cast hμ
      apply Set.mem_iUnion.mpr ⟨m, ?_⟩
      apply Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hm), ?_⟩
      exact ⟨x, Subtype.ext hx⟩
    · intro hμ
      obtain ⟨m, hμ⟩ := Set.mem_iUnion.mp hμ
      obtain ⟨hm, x, rfl⟩ := Set.mem_iUnion.mp hμ
      change (ofFin x).toFiniteMeasure.mass ≤ (N : ℝ≥0)
      rw [ofFin_mass]
      exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  rw [hset]
  apply (Finset.range (N + 1)).finite_toSet.isCompact_biUnion
  intro m _
  exact isCompact_range (continuous_ofFin (X := X) (m := m))

end Topology

end FinitePointMeasure
end Luce
