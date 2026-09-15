import Luce.Section6DominationMatrix
import Luce.Section6InsertionHolder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Exponent comparison for the actual gap kernel on its probability space. -/
theorem deleted_kernel_Lp_exponent_mono {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n) (q k r : ℕ) (hkr : k ≤ r) :
    eLpNorm (fun old => (deletedGapKernel w removed old i q).toReal)
      (k : ℝ≥0∞) (exponentialRace w) ≤
    eLpNorm (fun old => (deletedGapKernel w removed old i q).toReal)
      (r : ℝ≥0∞) (exponentialRace w) := by
  exact eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast hkr)
    (measurable_deletedGapKernel w removed i q).ennreal_toReal.aestronglyMeasurable

/-- One fixed matrix (deletion budget and exponent r) bounds every cylinder
of at most r distinct labels and distinct demanded ranks, including k=0. -/
theorem markedRankCylinder_probability_le_domination_matrix {n k r : ℕ}
    (w : Weights n) (hkr : k ≤ r) (u j : Fin k → Fin n)
    (hu : Injective u) (hj : Injective j) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} ≤
      ∏ a, ENNReal.ofReal (insertionDominationMatrix w r r (u a) (j a)) := by
  by_cases hk : k = 0
  · subst k
    simpa using (show exponentialRace w {clocks | MarkedRankCylinder u j clocks} ≤ 1 from prob_le_one)
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hremoved : (Finset.univ.image (u ∘ Tuple.sort j)).card ≤ r := by
    have hh : (Finset.univ.image (u ∘ Tuple.sort j)).card ≤ k := by
      exact Finset.card_image_le.trans (by simp)
    exact hh.trans hkr
  calc
    _ ≤ ∏ a, eLpNorm (fun old => (deletedGapKernel w (Finset.univ.image (u ∘ Tuple.sort j)) old
        ((u ∘ Tuple.sort j) a) (sortedMarkedGapIndex j a)).toReal)
        (k : ℝ≥0∞) (exponentialRace w) :=
      markedRankCylinder_probability_le_Lp_product w hkpos u j hu hj
    _ ≤ ∏ a, ENNReal.ofReal (insertionDominationMatrix w r r
        (u (Tuple.sort j a)) (j (Tuple.sort j a))) := by
      apply Finset.prod_le_prod'
      intro a ha
      apply (deleted_kernel_Lp_exponent_mono w _ _ _ k r hkr).trans
      have hshift : Nat.dist (sortedMarkedGapIndex j a) (j (Tuple.sort j a)).val ≤ r+1 := by
        have he := sortedMarkedGapIndex_add j hj a
        have ha' := a.isLt
        unfold Nat.dist
        omega
      exact deleted_kernel_le_insertionDominationMatrix w r r _ _ _ _ hremoved hshift
    _ = _ := Equiv.prod_comp (Tuple.sort j) (fun a => ENNReal.ofReal (insertionDominationMatrix w r r (u a) (j a)))

/-- The same cylinder estimate in real-valued probability notation. -/
theorem markedRankCylinder_real_probability_le_domination_matrix {n k r : ℕ}
    (w : Weights n) (hkr : k ≤ r) (u j : Fin k → Fin n)
    (hu : Injective u) (hj : Injective j) :
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} ≤
      ∏ a, insertionDominationMatrix w r r (u a) (j a) := by
  have he := markedRankCylinder_probability_le_domination_matrix w hkr u j hu hj
  rw [← ENNReal.ofReal_prod_of_nonneg (fun a _ => insertionDominationMatrix_nonneg w r r (u a) (j a))] at he
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [measureReal_def, ENNReal.toReal_ofReal
    (Finset.prod_nonneg (fun a _ => insertionDominationMatrix_nonneg w r r (u a) (j a)))] using ht

end Luce.Section6
