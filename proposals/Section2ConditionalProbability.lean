import Luce.DrawHistory
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Approved statement record: conditional probability identity, Section 2

Source: `fixed_points.tex:575`, `eq:predictable-p`, with the defining Luce law
from `fixed_points.tex:142`, `eq:luce-law`.

The user approved this statement. Its unchanged mathematical content is now
proved by `Luce.predictable_fixed_point_probability`, and checked against a
copy of this proposition in `audit/PredictableProbability.lean`. This record
remains outside the production imports. The full permutation masses specify
the model; the conditional-choice rule is not assumed.
-/

open MeasureTheory
universe u

namespace Luce.Section2ConditionalProposal

/-- Approved exact conditional expectation formula under the defining Luce
product law. Permutations have the discrete sigma algebra; equality of
conditional expectations is almost everywhere. -/
def PredictableProbabilityStatement : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [hP : IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n)),
    @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π →
    (∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ) →
    ∀ k : Fin n,
      P[(fun ω => if (π ω).symm k = k then (1 : ℝ) else 0)
          | drawHistory π k.val] =ᵐ[P]
        (fun ω =>
          (if k ≤ (π ω).symm k then w.rate k else 0) /
            w.total (remaining (π ω) k))

#print PredictableProbabilityStatement
#print axioms PredictableProbabilityStatement

end Luce.Section2ConditionalProposal
