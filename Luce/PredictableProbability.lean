import Luce.LuceNextDraw
import Luce.FiniteHistoryConditional
import Luce.ConditionalProbabilityBasics

/-! # The approved Luce conditional fixed-point probability

Source: `fixed_points.tex:575`, `eq:predictable-p`, under the defining full
permutation law `eq:luce-law`. The statement was approved in
`proposals/Section2ConditionalProbability.lean`. Conditional probabilities
are derived from the full masses, not assumed as a model field.
-/

open MeasureTheory
open scoped BigOperators
universe u

namespace Luce

/-- The exact approved arbitrary-space conditional expectation identity. -/
theorem predictable_fixed_point_probability
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ)
    (k : Fin n) :
    P[(fun ω => if (π ω).symm k = k then (1 : ℝ) else 0)
        | drawHistory π k.val] =ᵐ[P]
      (fun ω =>
        (if k ≤ (π ω).symm k then w.rate k else 0) /
          w.total (remaining (π ω) k)) := by
  classical
  have hconstant (σ τ : Equiv.Perm (Fin n))
      (h : prefixVector σ k.val = prefixVector τ k.val) :
      predictableChance w σ k = predictableChance w τ k :=
    predictableChance_eq_of_prefix_agreement w σ τ k
      ((prefixVector_eq_iff σ τ k.val).mp h)
  have hfiber (σ : Equiv.Perm (Fin n)) :
      (∑ τ ∈ Finset.univ.filter
          (fun τ : Equiv.Perm (Fin n) => prefixVector τ k.val = prefixVector σ k.val),
        P.real {ω | π ω = τ} * (if τ.symm k = k then (1 : ℝ) else 0)) =
      predictableChance w σ k *
        ∑ τ ∈ Finset.univ.filter
          (fun τ : Equiv.Perm (Fin n) => prefixVector τ k.val = prefixVector σ k.val),
          P.real {ω | π ω = τ} := by
    simp_rw [hMass]
    exact fixed_point_mass_fiber_identity w σ k
  have h := condExp_finite_history_of_representatives (P := P) π hπ
    (fun σ => prefixVector σ k.val)
    (fun σ => if σ.symm k = k then (1 : ℝ) else 0)
    (fun σ => predictableChance w σ k) hconstant hfiber
  rw [← drawHistory_eq_comap_prefixVector π k.val] at h
  simpa only [predictableChance_formula] using h

end Luce
