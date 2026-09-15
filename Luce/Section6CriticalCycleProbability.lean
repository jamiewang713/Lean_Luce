import Luce.Section6CriticalShiftLog
import Luce.Section6CriticalCycleKernel
import Luce.Section6CriticalBlocks
import Luce.Section6DominationMatrixCylinder
import Luce.Section5MaximumCylinder

noncomputable section
open MeasureTheory Function
open scoped BigOperators
namespace Luce.Section6

theorem critical_retained_probability_le_matrix {n : ℕ} (w : Weights n)
    (k : ℕ) (S : Finset (Fin n)) (v : Fin n) :
    (exponentialRace w).real (retainedMaximumCycleEvent k S v) ≤
      ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        Injective u ∧ (∀ a, u a < v) ∧ ∀ a, (Fin.cons v u : Fin (k+1) → Fin n) a ∈ S),
        ∏ a : Fin (k+1), insertionDominationMatrix w (k+1) (k+1)
          ((Fin.cons v u : Fin (k+1) → Fin n) a) ((Fin.snoc u v : Fin (k+1) → Fin n) a) := by
  classical
  let s := Finset.univ.filter (fun u : Fin k → Fin n =>
    Injective u ∧ (∀ a, u a < v) ∧ ∀ a, (Fin.cons v u : Fin (k+1) → Fin n) a ∈ S)
  let A := fun u : Fin k → Fin n => {e | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) e}
  have hcover : exponentialRace w (retainedMaximumCycleEvent k S v) ≤
      ∑ u ∈ s, exponentialRace w (A u) := by
    apply (measure_mono_ae (t := ⋃ u ∈ s, A u) ?_).trans (measure_biUnion_finset_le s A)
    filter_upwards [exponentialRace_injective_ae w] with e he
    intro h
    obtain ⟨u,hu,huv,hS,hass⟩ := exists_retained_maximum_cycle_tail
      (raceRankPermutation e) S v h.1 h.2.1 h.2.2
    apply Set.mem_iUnion.mpr
    refine ⟨u,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu,huv,hS⟩,?_⟩⟩
    intro a
    have hh := congrArg Fin.val (hass a)
    rw [raceRankPermutation_eq e he] at hh
    change clockBeforeCount e (e ((Fin.cons v u : Fin (k+1) → Fin n) a)) =
      ((Fin.snoc u v : Fin (k+1) → Fin n) a).val at hh
    change 1+clockBeforeCount e (e ((Fin.cons v u : Fin (k+1) → Fin n) a)) =
      ((Fin.snoc u v : Fin (k+1) → Fin n) a).val+1
    omega
  have hreal := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top _ _)) hcover
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at hreal
  apply hreal.trans
  apply Finset.sum_le_sum
  intro u hu
  obtain ⟨hui,huv,hS⟩ := (Finset.mem_filter.mp hu).2
  have hvnot : v ∉ Set.range u := by rintro ⟨a,ha⟩; exact (ne_of_lt (huv a)) ha
  exact markedRankCylinder_real_probability_le_domination_matrix w le_rfl
    (Fin.cons v u) (Fin.snoc u v) (Fin.cons_injective_iff.mpr ⟨hvnot,hui⟩)
    (Fin.snoc_injective_iff.mpr ⟨hui,hvnot⟩)

theorem critical_tuple_weight_sum {n k : ℕ} (v : Fin n) {a : ℝ} (ha : 0 < a)
    (S : Finset (Fin k → Fin n)) (hS : ∀ u ∈ S, ∀ i, u i ≤ v) :
    (∑ u ∈ S, ∏ i, (1/((u i).val+1 : ℝ))*
      (((u i).val+1 : ℝ)/((v.val : ℝ)+1))^a) ≤ (1+1/a)^k := by
  classical
  let f : Fin n → ℝ := fun i => if i ≤ v then
    (1/((i.val : ℝ)+1))*(((i.val : ℝ)+1)/((v.val : ℝ)+1))^a else 0
  have hf (i : Fin n) : 0 ≤ f i := by dsimp [f]; split_ifs <;> positivity
  have hsum : (∑ i, f i) ≤ 1+1/a := by
    have he : (∑ i, f i) = ∑ m ∈ Finset.Icc 1 (v.val+1),
        (1/(m : ℝ))*((m : ℝ)/(v.val+1 : ℕ))^a := by
      rw [← critical_block_sum (n := n) (by omega : 1 ≤ 1) v.isLt]
      simp only [f,criticalBlock,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      have hh : i ≤ v ↔ 1 ≤ i.val+1 ∧ i.val+1 ≤ v.val+1 := by simp only [Fin.le_def]; omega
      simp only [hh,Nat.cast_add,Nat.cast_one]
    rw [he]
    exact right_excursion_kernel_sum ha (by omega) (by omega)
  calc
    _ = ∑ u ∈ S, ∏ i, f (u i) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.prod_congr rfl
      intro i _
      simp only [f,if_pos (hS u hu i)]
    _ ≤ ∑ u : Fin k → Fin n, ∏ i, f (u i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun u _ _ => Finset.prod_nonneg (fun i _ => hf _))
    _ = (∑ i, f i)^k := by rw [← Fintype.prod_sum]; simp
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => hf i)) hsum k

end Luce.Section6
