import Luce.Model

/-!
# Remaining labels and the preceding draw history

Positions and labels use the zero-based indexing of `Fin n`.
-/

namespace Luce

/-- A label remains before position `k` exactly when no earlier draw selected it. -/
theorem inverse_ge_iff_no_earlier_draw {n : ℕ} (π : Equiv.Perm (Fin n))
    (k i : Fin n) :
    k ≤ π.symm i ↔ ∀ j : Fin n, j < k → π j ≠ i := by
  constructor
  · intro h j hj hji
    have heq : j = π.symm i := by
      simpa only [Equiv.symm_apply_apply] using congrArg π.symm hji
    exact (not_lt_of_ge h) (heq ▸ hj)
  · intro h
    apply le_of_not_gt
    intro hlt
    exact h (π.symm i) hlt (π.apply_symm_apply i)

end Luce
