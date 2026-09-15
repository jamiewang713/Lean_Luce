import Luce.Sections1To7

/-! The approved full proposition is copied exactly to verify the production
theorem's mathematical signature. It is proved below, not assumed. -/

open MeasureTheory
universe u

namespace Luce.Section2ConditionalLockedAudit

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

theorem approved_statement : PredictableProbabilityStatement.{u} :=
  Luce.predictable_fixed_point_probability

#print approved_statement
#print axioms approved_statement
end Luce.Section2ConditionalLockedAudit

#print Luce.Weights.removeFirst
#print Luce.Weights.sum_rate_perm
#print Luce.Weights.decomposeFin_tail_sum
#print Luce.Weights.mass_decomposeFin
#print Luce.Weights.sum_mass
#print Luce.prefixAgrees
#print Luce.prefixMass
#print Luce.prefixAgrees_zero
#print Luce.prefixAgrees_self
#print Luce.prefixMass_zero
#print Luce.prefixMass_full
#print Luce.prefixAgrees_decomposeFin
#print Luce.prefixMass_decomposeFin
#print Luce.sum_mass_prefix
#print Luce.remaining_total_eq_tail_sum
#print Luce.prefixMass_succ
#print Luce.prefixMass_eq_of_prefix_agreement
#print Luce.exists_prefixAgrees_next_eq
#print Luce.prefixAgrees_succ_iff
#print Luce.sum_mass_prefix_next
#print Luce.fixed_point_mass_fiber_identity
#print Luce.prefixVector
#print Luce.drawHistory_eq_comap_prefixVector
#print Luce.prefixVector_eq_iff
#print Luce.remaining_eq_of_prefix_agreement
#print Luce.predictableChance_eq_of_prefix_agreement
#print Luce.integrable_finite_state
#print Luce.integral_finite_state
#print Luce.condExp_finite_history
#print Luce.condExp_finite_history_of_representatives
#print Luce.drawHistory_le
#print Luce.measurable_predictableChance_history
#print Luce.integrable_predictableChance
#print Luce.integrable_fixed_point_indicator
#print Luce.predictable_fixed_point_probability

#print axioms Luce.Weights.removeFirst
#print axioms Luce.Weights.sum_rate_perm
#print axioms Luce.Weights.decomposeFin_tail_sum
#print axioms Luce.Weights.mass_decomposeFin
#print axioms Luce.Weights.sum_mass
#print axioms Luce.prefixAgrees
#print axioms Luce.prefixMass
#print axioms Luce.prefixAgrees_zero
#print axioms Luce.prefixAgrees_self
#print axioms Luce.prefixMass_zero
#print axioms Luce.prefixMass_full
#print axioms Luce.prefixAgrees_decomposeFin
#print axioms Luce.prefixMass_decomposeFin
#print axioms Luce.sum_mass_prefix
#print axioms Luce.remaining_total_eq_tail_sum
#print axioms Luce.prefixMass_succ
#print axioms Luce.prefixMass_eq_of_prefix_agreement
#print axioms Luce.exists_prefixAgrees_next_eq
#print axioms Luce.prefixAgrees_succ_iff
#print axioms Luce.sum_mass_prefix_next
#print axioms Luce.fixed_point_mass_fiber_identity
#print axioms Luce.prefixVector
#print axioms Luce.drawHistory_eq_comap_prefixVector
#print axioms Luce.prefixVector_eq_iff
#print axioms Luce.remaining_eq_of_prefix_agreement
#print axioms Luce.predictableChance_eq_of_prefix_agreement
#print axioms Luce.integrable_finite_state
#print axioms Luce.integral_finite_state
#print axioms Luce.condExp_finite_history
#print axioms Luce.condExp_finite_history_of_representatives
#print axioms Luce.drawHistory_le
#print axioms Luce.measurable_predictableChance_history
#print axioms Luce.integrable_predictableChance
#print axioms Luce.integrable_fixed_point_indicator
#print axioms Luce.predictable_fixed_point_probability
