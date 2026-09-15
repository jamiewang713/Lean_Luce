import Mathlib.Data.Finset.Card

/-!
# Luce permutations

Starting point for the formalization of `fixed_points.tex`.
The example below checks that mathlib is available; it is not a paper result.
-/

namespace Luce

example (n : ℕ) : (Finset.range n).card = n := by
  simp

end Luce
