import Luce.Section6CoreDepthEquivalence

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem core_ideal_category_sum_reindex {n A B k : ℕ} (hA : 1 ≤ A) (hB : B ≤ n)
    (side : Corner) (behavior : EndpointBehavior) (window : CoreRootWindow) :
    (∑ x : Fin (k+1) → CollisionCore n A B side,
      if Function.Injective (fun j => (x j).val) ∧
        window.Allows n (categorySetRootDepth side (Finset.univ.image (fun j => (x j).val))) then
        collisionCycleWeight (fun a b : CollisionCore n A B side =>
          localIdealKernel side behavior (cornerDistance side a.val) (cornerDistance side b.val)) k x
      else 0) =
    ∑ a : IdealDepthTuple A B k,
      if Function.Injective (fun j => (a j).val) ∧
        window.Allows n (idealTupleRoot side k (fun j => (a j).val)) then
        idealCycleWeight side behavior k (fun j => (a j).val) else 0 := by
  let e : (Fin (k+1) → CollisionCore n A B side) ≃ IdealDepthTuple A B k :=
    Equiv.piCongrRight (fun _ => coreDepthEquiv hA hB side)
  apply Fintype.sum_equiv e
  intro x
  simp only [category_set_root_eq_tuple_root, core_tuple_labels_injective_iff]
  rfl

/-- The exact ideal category mean is the corresponding labelled core sum.
In particular the root restriction is the actual largest-label restriction. -/
theorem core_category_mean_eq_tuple_sum {n : ℕ}
    (hA : 1 ≤ idealCoreLower n) (hB : idealCoreUpper n ≤ n)
    (left right : EndpointBehavior) (c : CoreCycleCategory) :
    coreCategoryIdealMean left right n c =
      (∑ x : Fin (c.lengthIndex+1) → CollisionCore n (idealCoreLower n) (idealCoreUpper n) c.side,
        if Function.Injective (fun j => (x j).val) ∧
          c.rootWindow.Allows n (categorySetRootDepth c.side (Finset.univ.image (fun j => (x j).val))) then
          collisionCycleWeight (fun a b : CollisionCore n (idealCoreLower n) (idealCoreUpper n) c.side =>
            localIdealKernel c.side (cornerBehavior left right c.side)
              (cornerDistance c.side a.val) (cornerDistance c.side b.val)) c.lengthIndex x else 0) /
        ((c.lengthIndex : ℝ)+1) := by
  rw [core_ideal_category_sum_reindex hA hB]
  cases c with
  | mk side k window =>
    cases window with
    | all => simp [coreCategoryIdealMean, idealTrace, Finset.sum_filter, CoreRootWindow.Allows]
    | interval lo hi =>
      simp [coreCategoryIdealMean, idealRootTrace, Finset.sum_filter, CoreRootWindow.Allows]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      split_ifs with h
      · exact (if_pos h).symm
      · exact (if_neg h).symm

end Luce.Section6
