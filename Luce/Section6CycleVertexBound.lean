import Luce.Section6DominationMatrixCylinder
import Luce.Section5LowCycleRows

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace Luce.Section6

/-- Generic application of the concrete cylinder bound: a target maximum
and the matrix row sum bound control the probability of a cycle through v.
Concrete profile applications must discharge both numerical premises. -/
theorem cycle_vertex_probability_le_matrix_rows {n k r : ℕ} (w : Weights n)
    (hkr : k+1 ≤ r) (v : Fin n) {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hrow : ∀ i, ∑ j, insertionDominationMatrix w r r i j ≤ C)
    (htarget : ∀ i, insertionDominationMatrix w r r i v ≤ T) :
    (exponentialRace w).real {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1} ≤ T*C^k := by
  classical
  let M := insertionDominationMatrix w r r
  let s := Finset.univ.filter (fun u : Fin k → Fin n => Injective u ∧ ∀ a, u a ≠ v)
  have hM (i j : Fin n) : 0 ≤ M i j := insertionDominationMatrix_nonneg w r r i j
  have hcylinder : ∀ u ∈ s,
      (exponentialRace w).real {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks} ≤
        T*forwardPathWeight M v u := by
    intro u hu
    obtain ⟨huinj, huv⟩ := (Finset.mem_filter.mp hu).2
    have hvnot : v ∉ Set.range u := by rintro ⟨a, ha⟩; exact huv a ha
    have ht := markedRankCylinder_real_probability_le_domination_matrix w hkr
      (Fin.cons v u) (Fin.snoc u v)
      (Fin.cons_injective_iff.mpr ⟨hvnot, huinj⟩)
      (Fin.snoc_injective_iff.mpr ⟨huinj, hvnot⟩)
    have hid : (∏ a : Fin (k+1), M ((Fin.cons v u : Fin (k+1) → Fin n) a)
        ((Fin.snoc u v : Fin (k+1) → Fin n) a)) =
        forwardPathWeight M v u * M ((Fin.cons v u : Fin (k+1) → Fin n) (Fin.last k)) v := by
      simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, forwardPathWeight]
    change _ ≤ ∏ a : Fin (k+1), M ((Fin.cons v u : Fin (k+1) → Fin n) a)
      ((Fin.snoc u v : Fin (k+1) → Fin n) a) at ht
    rw [hid] at ht
    exact ht.trans (by
      rw [mul_comm T]
      exact mul_le_mul_of_nonneg_left (htarget _) (Finset.prod_nonneg (fun a _ => hM _ _)))
  calc
    _ ≤ ∑ u ∈ s, (exponentialRace w).real
        {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks} :=
      cycle_period_real_probability_le_sum_cylinders w v
    _ ≤ ∑ u ∈ s, T*forwardPathWeight M v u := Finset.sum_le_sum hcylinder
    _ ≤ ∑ u : Fin k → Fin n, T*forwardPathWeight M v u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun u _ _ => mul_nonneg hT (Finset.prod_nonneg (fun a _ => hM _ _)))
    _ = T*(∑ u : Fin k → Fin n, forwardPathWeight M v u) := (Finset.mul_sum _ _ _).symm
    _ ≤ T*C^k := mul_le_mul_of_nonneg_left (forwardPathWeight_sum_le M hM C hC hrow k v) hT

end Luce.Section6
