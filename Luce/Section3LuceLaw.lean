import Luce.Section3RaceDrawLaw

/-!
# Transfer from the exponential race to an arbitrary Luce-law model

The full permutation masses determine a probability measure on the finite
permutation space. This proves that the canonical race representation recovers
every model in the source's defining Luce law, with no coupling assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Luce

/-- The defining Luce masses identify the law of any measurable permutation
with the law of the sorted independent exponential clocks. -/
theorem luce_map_eq_raceDraw {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ) :
    @Measure.map Ω (Equiv.Perm (Fin n)) mΩ ⊤ π P =
      @Measure.map (Fin n → ℝ) (Equiv.Perm (Fin n)) inferInstance ⊤
        raceDraw (exponentialRace w) := by
  classical
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  change P.map π = (exponentialRace w).map raceDraw
  apply Measure.ext_of_measureReal_singleton
  intro σ
  rw [map_measureReal_apply hπ (measurableSet_singleton σ),
    map_measureReal_apply (measurable_raceDraw n) (measurableSet_singleton σ)]
  exact (hMass σ).trans (raceDraw_mass w σ).symm

end Luce
