import Luce.Section6LocalKernelDefinitions
import Mathlib.GroupTheory.Perm.Fin

/-! Literal deterministic ideal sums from Lemma 6.8. Index k denotes
length k+1. The sum is over ordered distinct tuples and divided by k+1,
as in the manuscript. No asymptotic approximation enters these definitions. -/
noncomputable section
open scoped BigOperators
namespace Luce.Section6

abbrev IdealDepthTuple (A B k : ℕ) := Fin (k+1) → ↥(Finset.Icc A B)

def idealCycleWeight (side : Corner) (behavior : EndpointBehavior) (k : ℕ)
    (a : Fin (k+1) → ℕ) : ℝ :=
  ∏ j, localIdealKernel side behavior (a j) (a (finRotate (k+1) j))

/-- Largest-label roots have minimum right depth and maximum left depth. -/
def idealTupleRoot (side : Corner) (k : ℕ) (a : Fin (k+1) → ℕ) : ℕ :=
  match side with
  | .right => Finset.univ.inf' Finset.univ_nonempty a
  | .left => Finset.univ.sup' Finset.univ_nonempty a

def idealTrace (side : Corner) (behavior : EndpointBehavior) (k A B : ℕ) : ℝ := by
  classical
  exact (∑ a ∈ Finset.univ.filter (fun a : IdealDepthTuple A B k =>
    Function.Injective (fun j => (a j).val)),
      idealCycleWeight side behavior k (fun j => (a j).val)) / ((k : ℝ)+1)

def idealRootTrace (side : Corner) (behavior : EndpointBehavior)
    (k A B : ℕ) (lo hi : ℝ) : ℝ := by
  classical
  exact (∑ a ∈ Finset.univ.filter (fun a : IdealDepthTuple A B k =>
    Function.Injective (fun j => (a j).val) ∧
      lo < (idealTupleRoot side k (fun j => (a j).val) : ℝ) ∧
      (idealTupleRoot side k (fun j => (a j).val) : ℝ) ≤ hi),
      idealCycleWeight side behavior k (fun j => (a j).val)) / ((k : ℝ)+1)

def idealCoreLower (n : ℕ) : ℕ :=
  ⌈Real.exp ((Real.log (n : ℝ))^(1/4 : ℝ))⌉₊

def idealCoreUpper (n : ℕ) : ℕ :=
  ⌊(n : ℝ)/(idealCoreLower n : ℝ)⌋₊

def idealSpatialTrace (side : Corner) (behavior : EndpointBehavior)
    (k n : ℕ) (a b : ℝ) : ℝ :=
  idealRootTrace side behavior k (idealCoreLower n) (idealCoreUpper n)
    ((n : ℝ)^a) ((n : ℝ)^b)

end Luce.Section6
