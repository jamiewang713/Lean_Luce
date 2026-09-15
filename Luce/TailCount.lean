import Luce.Assumptions
import Luce.ApprovedRankIntegral
import Luce.EndpointAsymptotic

/-! # The approved spatial tail count

Source: `fixed_points.tex`, Section 4, `eq:tail-tightness`.
The definition and the general-space tail-tightness statement were approved
by the user. The paper's label corresponding to `k : Fin n` is `k.val + 1`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Luce

/-- The exact number of fixed-point atoms in `(α, 1]`. -/
noncomputable def tailFixedPointCount {n : ℕ}
    (e : Fin n → ℝ) (α : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun k : Fin n =>
    α * (n : ℝ) < (k.val : ℝ) + 1 ∧ rankOf e k = k.val + 1).card

end Luce
