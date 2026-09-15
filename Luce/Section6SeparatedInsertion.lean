import Luce.Section6GapOrderPartition

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace Luce.Section6

/-- Full-rank separation implies distinct selected background gaps after
deleting all marks. No endpoint or concentration assumption is used. -/
theorem sorted_gap_injective_of_separated {n s r : ℕ} (hs : s ≤ r)
    (j : Fin s → Fin n) (hj : Injective j)
    (hsep : ∀ a b, a ≠ b → 2*r < Nat.dist (j a).val (j b).val) :
    Injective (sortedMarkedGapIndex j) := by
  intro a b hab
  by_contra hne
  have hne' : Tuple.sort j a ≠ Tuple.sort j b := fun h => hne ((Tuple.sort j).injective h)
  have hdist := hsep _ _ hne'
  have ha := sortedMarkedGapIndex_add j hj a
  have hb := sortedMarkedGapIndex_add j hj b
  have ha' := a.isLt
  have hb' := b.isLt
  unfold Nat.dist at hdist
  omega

/-- Exact product inside a single expectation for separated demanded ranks.
This does not replace the expectation of a product by a product of expectations. -/
theorem separated_cylinder_eq_gap_product {n s r : ℕ} (w : Weights n) (hs : s ≤ r)
    (u j : Fin s → Fin n) (hu : Injective u) (hj : Injective j)
    (hsep : ∀ a b, a ≠ b → 2*r < Nat.dist (j a).val (j b).val) :
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} =
      ∫ old, (∏ a, deletedGapKernel w (Finset.univ.image (u ∘ Tuple.sort j)) old
        (u (Tuple.sort j a)) (sortedMarkedGapIndex j a)).toReal ∂exponentialRace w := by
  rw [markedRankCylinder_real_probability_eq_sortedOrderedInsertion w u j hu hj]
  have hq := (sortedMarkedGapIndex_monotone j hj).strictMono_of_injective
    (sorted_gap_injective_of_separated hs j hj hsep)
  apply integral_congr_ae
  filter_upwards [] with old
  rw [orderedInsertionKernel_eq_product_of_strictMono w _ _ (hu.comp (Tuple.sort j).injective) hq old]
  rfl

end Luce.Section6
