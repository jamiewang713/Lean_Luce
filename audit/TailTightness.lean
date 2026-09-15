import Luce

/-! The approved proposal is reproduced below to check definitional equality
of both the count and the full theorem type with the production declarations.
No proposition is assumed: `approved_statement` is proved by the production
theorem, and the count equality is checked by `rfl`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
universe u

namespace Luce.Section4LockedAudit

noncomputable def tailFixedPointCount {n : ℕ}
    (e : Fin n → ℝ) (α : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun k : Fin n =>
    α * (n : ℝ) < (k.val : ℝ) + 1 ∧ rankOf e k = k.val + 1).card

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

theorem approved_count {n : ℕ} (e : Fin n → ℝ) (α : ℝ) :
    tailFixedPointCount e α = Luce.tailFixedPointCount e α := rfl

theorem approved_statement : TailTightnessStatement.{u} := Luce.tail_fixed_point_tightness

#print approved_statement
#print axioms approved_statement
#print axioms approved_count
end Luce.Section4LockedAudit

#print Luce.tailFixedPointCount
#print Luce.measurable_tailFixedPointCount
#print Luce.tailFixedPointCount_le
#print Luce.integrable_tailFixedPointCount
#print Luce.tailFixedPointCount_probability_le_expectation
#print Luce.tailFixedPointCount_probability_eq
#print Luce.rankOf_eq_raceRank_for_tail
#print Luce.spatial_tail_iff_terminal_index
#print Luce.tailFixedPointCount_eq_terminalFixedPointCount
#print Luce.NormalizedWeights.sum_rates_succ
#print Luce.EndpointAssumption.eventually_terminal_rates
#print Luce.endpointAssumption_epsilon_estimate
#print Luce.endpointAssumption_epsilon_estimate_bounded
#print Luce.tendsto_zero_of_endpoint_power_bound
#print Luce.tail_probability_le_epsilonTailExpectation
#print Luce.tail_fixed_point_tightness

#print axioms Luce.tailFixedPointCount
#print axioms Luce.measurable_tailFixedPointCount
#print axioms Luce.tailFixedPointCount_le
#print axioms Luce.integrable_tailFixedPointCount
#print axioms Luce.tailFixedPointCount_probability_le_expectation
#print axioms Luce.tailFixedPointCount_probability_eq
#print axioms Luce.rankOf_eq_raceRank_for_tail
#print axioms Luce.spatial_tail_iff_terminal_index
#print axioms Luce.tailFixedPointCount_eq_terminalFixedPointCount
#print axioms Luce.NormalizedWeights.sum_rates_succ
#print axioms Luce.EndpointAssumption.eventually_terminal_rates
#print axioms Luce.endpointAssumption_epsilon_estimate
#print axioms Luce.endpointAssumption_epsilon_estimate_bounded
#print axioms Luce.tendsto_zero_of_endpoint_power_bound
#print axioms Luce.tail_probability_le_epsilonTailExpectation
#print axioms Luce.tail_fixed_point_tightness

#print axioms Luce.endpoint_fixedPoint_expectation_bound
#print axioms Luce.endpoint_fixedPoint_expectation_power_bound
#print axioms Luce.epsilonTailExpectation_eventually_le
#print axioms Luce.epsilonTailExpectation_power_limsup
#print axioms Luce.rank_integral
