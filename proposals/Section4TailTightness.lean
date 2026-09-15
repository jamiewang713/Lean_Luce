import Luce.Assumptions
import Luce.ApprovedRankIntegral
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Approved statement record: `eq:tail-tightness`

Source: `fixed_points.tex`, Section 4, equation `eq:tail-tightness`.
The user approved this count and proposition. This historical statement
record stays outside the library imports. The production proof is
`Luce.tail_fixed_point_tightness`; `audit/TailTightness.lean` checks its type
against the statement below. This record itself only defines a proposition.

The locked proposition uses the approved assumptions and rank definition.
Each row may have its own probability space, with independence only within
that row. No profile-convergence hypothesis is needed for this endpoint step.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

universe u

namespace Luce.Section4Proposal

/-- Approved exact count of the fixed-point atoms in `(α, 1]`.
The paper's label is `k.val + 1`. Row zero has no labels, so its count is zero.
For a positive row size, `α * n < k.val + 1` is exactly `(k.val + 1) / n > α`.
-/
noncomputable def tailFixedPointCount {n : ℕ}
    (e : Fin n → ℝ) (α : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun k : Fin n =>
    α * (n : ℝ) < (k.val : ℝ) + 1 ∧ rankOf e k = k.val + 1).card

/-- The approved full type of the theorem. This definition does not
provide a proof or an assumption that the proposition holds. -/
def TailTightnessStatement : Prop :=
  ∀ (Ω : ℕ → Type u) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [hP : ∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray),
    NormalizedWeights w → EndpointAssumption w →
    ∀ E : (n : ℕ) → Fin n → Ω n → ℝ,
      (∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n)) →
      (∀ n, iIndepFun (E n) (P n)) →
      Tendsto
        (fun α : ℝ => limsup
          (fun n : ℕ => (P n).real
            {ω | 0 < tailFixedPointCount (fun i => E n i ω) α}) atTop)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))

#print TailTightnessStatement
#print axioms tailFixedPointCount
#print axioms TailTightnessStatement

end Luce.Section4Proposal
