import Luce.Section6IdealTraceDefinitions

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem sum_tuple_restrict68 {S T : Finset ℕ} (hST : S ⊆ T) (d : ℕ)
    (F : (Fin d → ℕ) → ℝ) :
    (∑ x : Fin d → ↥T, if ∀ j, (x j).val ∈ S then F (fun j => (x j).val) else 0) =
      ∑ x : Fin d → ↥S, F (fun j => (x j).val) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun x _ j => (⟨(x j).val, hST (x j).property⟩ : ↥T))
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun j => (x j).property
  · intro x _ y _ h
    funext j
    exact Subtype.ext (congrArg (fun z => (z j).val) h)
  · intro y hy
    have h := (Finset.mem_filter.mp hy).2
    refine ⟨fun j => ⟨(y j).val, h j⟩, Finset.mem_univ _, ?_⟩
    rfl
  · intro x _
    rfl

theorem idealTrace_restrict68 (side : Corner) (behavior : EndpointBehavior)
    (k : ℕ) {A B P Q : ℕ} (hAP : A ≤ P) (hQB : Q ≤ B) :
    idealTrace side behavior k P Q =
      (∑ x : IdealDepthTuple A B k,
        if (∀ j, P ≤ (x j).val ∧ (x j).val ≤ Q) ∧ Function.Injective (fun j => (x j).val)
        then idealCycleWeight side behavior k (fun j => (x j).val) else 0)/((k : ℝ)+1) := by
  classical
  have hST : Finset.Icc P Q ⊆ Finset.Icc A B := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨hAP.trans (Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hQB⟩
  have h := sum_tuple_restrict68 hST (k+1) (fun x =>
    if Function.Injective x then idealCycleWeight side behavior k x else 0)
  unfold idealTrace
  rw [Finset.sum_filter]
  congr 1
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.mem_Icc]
  split_ifs <;> simp_all

theorem idealTupleRoot_right_gt68 (k P : ℕ) (x : Fin (k+1) → ℕ) :
    P < idealTupleRoot .right k x ↔ ∀ j, P < x j := by
  simp [idealTupleRoot, Finset.lt_inf'_iff]

theorem idealTupleRoot_left_le68 (k Q : ℕ) (x : Fin (k+1) → ℕ) :
    idealTupleRoot .left k x ≤ Q ↔ ∀ j, x j ≤ Q := by
  simp [idealTupleRoot, Finset.sup'_le_iff]

theorem idealRootTrace_floor68 (side : Corner) (behavior : EndpointBehavior)
    (k A B : ℕ) {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) :
    idealRootTrace side behavior k A B lo hi =
      idealRootTrace side behavior k A B (⌊lo⌋₊ : ℝ) (⌊hi⌋₊ : ℝ) := by
  classical
  unfold idealRootTrace
  congr 1
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.floor_lt hlo, ← Nat.le_floor_iff hhi, Nat.cast_lt, Nat.cast_le]
  · intro x _
    rfl

theorem idealRootTrace_right_sub68 (behavior : EndpointBehavior) (k : ℕ)
    {A B P Q : ℕ} (hAP : A ≤ P+1) (hPQ : P ≤ Q) :
    idealRootTrace .right behavior k A B (P : ℝ) (Q : ℝ) =
      idealTrace .right behavior k (P+1) B-idealTrace .right behavior k (Q+1) B := by
  classical
  rw [idealTrace_restrict68 .right behavior k hAP le_rfl,
    idealTrace_restrict68 .right behavior k (hAP.trans (Nat.add_le_add_right hPQ 1)) le_rfl]
  unfold idealRootTrace
  rw [Finset.sum_filter, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have hb : ∀ j, (x j).val ≤ B := fun j => (Finset.mem_Icc.mp (x j).property).2
  have hP : (∀ j, P+1 ≤ (x j).val ∧ (x j).val ≤ B) ↔
      P < idealTupleRoot .right k (fun j => (x j).val) := by
    rw [idealTupleRoot_right_gt68]
    simp only [hb, and_true, Nat.add_one_le_iff]
  have hQ : (∀ j, Q+1 ≤ (x j).val ∧ (x j).val ≤ B) ↔
      Q < idealTupleRoot .right k (fun j => (x j).val) := by
    rw [idealTupleRoot_right_gt68]
    simp only [hb, and_true, Nat.add_one_le_iff]
  simp only [hP, hQ, Nat.cast_lt, Nat.cast_le]
  split_ifs <;> simp_all <;> omega

theorem idealRootTrace_left_sub68 (behavior : EndpointBehavior) (k : ℕ)
    {A B P Q : ℕ} (hPQ : P ≤ Q) (hQB : Q ≤ B) :
    idealRootTrace .left behavior k A B (P : ℝ) (Q : ℝ) =
      idealTrace .left behavior k A Q-idealTrace .left behavior k A P := by
  classical
  rw [idealTrace_restrict68 .left behavior k le_rfl hQB,
    idealTrace_restrict68 .left behavior k le_rfl (hPQ.trans hQB)]
  unfold idealRootTrace
  rw [Finset.sum_filter, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have ha : ∀ j, A ≤ (x j).val := fun j => (Finset.mem_Icc.mp (x j).property).1
  have hP : (∀ j, A ≤ (x j).val ∧ (x j).val ≤ P) ↔
      idealTupleRoot .left k (fun j => (x j).val) ≤ P := by
    rw [idealTupleRoot_left_le68]
    simp only [ha, true_and]
  have hQ : (∀ j, A ≤ (x j).val ∧ (x j).val ≤ Q) ↔
      idealTupleRoot .left k (fun j => (x j).val) ≤ Q := by
    rw [idealTupleRoot_left_le68]
    simp only [ha, true_and]
  simp only [hP, hQ, Nat.cast_lt, Nat.cast_le]
  split_ifs <;> simp_all <;> omega

end Luce.Section6
