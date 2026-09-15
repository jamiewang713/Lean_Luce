import Luce.Section2HistoryPredictability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Derived analytic obligations for the Luce conditional probability

The approved target supplies a measurable permutation and a probability
measure. History inclusion, measurability, and integrability follow from
these inputs; none is added as an extra hypothesis of that target.
-/

open MeasureTheory
universe u

namespace Luce

lemma drawHistory_le {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π) (m : ℕ) :
    drawHistory π m ≤ mΩ := by
  apply iSup_le
  intro j
  apply iSup_le
  intro _
  have hj : @Measurable (Equiv.Perm (Fin n)) (Fin n) ⊤ ⊤ (fun σ => σ j) :=
    fun _ _ => trivial
  exact (hj.comp hπ).comap_le

lemma measurable_predictableChance_history {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (k : Fin n) :
    Measurable[drawHistory π k.val] (fun ω => predictableChance w (π ω) k) := by
  simp_rw [predictableChance_formula]
  exact (Measurable.ite (measurableSet_label_available π k k)
    measurable_const measurable_const).div (measurable_remaining_weight w π k)

lemma integrable_predictableChance {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π) (k : Fin n) :
    Integrable (fun ω => predictableChance w (π ω) k) P := by
  refine ⟨((measurable_predictableChance_history w π k).mono
    (drawHistory_le π hπ k.val) le_rfl).aestronglyMeasurable, ?_⟩
  exact HasFiniteIntegral.of_mem_Icc 0 1 (ae_of_all P fun ω =>
    ⟨w.choice_nonneg (remaining (π ω) k) k, w.choice_le_one (remaining (π ω) k) k⟩)

lemma integrable_fixed_point_indicator {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π) (k : Fin n) :
    Integrable (fun ω => if (π ω).symm k = k then (1 : ℝ) else 0) P := by
  have hs : MeasurableSet {ω | (π ω).symm k = k} :=
    hπ (show MeasurableSet[(⊤ : MeasurableSpace (Equiv.Perm (Fin n)))]
      {σ | σ.symm k = k} from trivial)
  refine ⟨(Measurable.ite hs measurable_const measurable_const).aestronglyMeasurable, ?_⟩
  exact HasFiniteIntegral.of_mem_Icc 0 1 (ae_of_all P fun ω => by
    split_ifs <;> simp)

end Luce
