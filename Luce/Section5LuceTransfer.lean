import Luce.Section5RaceConclusion
import Luce.Section3LuceLaw

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace Luce

/-- Draw order and rank order are inverse permutations; their actual cycle
counts coincide. This identity also covers the common extension at ties. -/
theorem cycleCountVector_raceDraw_eq_rank {n : ℕ} (z : Fin n → ℝ) (L : ℕ) :
    cycleCountVector L (raceDraw z) = cycleCountVector L (raceRankPermutation z) := by
  classical
  funext ell
  by_cases h : Function.Injective z
  · simp only [cycleCountVector, raceDraw_eq z h, raceRankPermutation_eq z h,
      drawPermutation, Section5.cycleCount_symm]
  · simp only [cycleCountVector, raceDraw, raceRankPermutation, h, dite_false]

theorem luce_cycle_vector_map_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ, P.real {ω | π ω = σ} = w.mass σ) (L : ℕ) :
    P.map (fun ω => cycleCountVector L (π ω)) =
      (exponentialRace w).map (fun z => cycleCountVector L (raceRankPermutation z)) := by
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hC : Measurable (cycleCountVector (n := n) L) := fun _ _ => trivial
  calc
    _ = (P.map π).map (cycleCountVector L) := (Measure.map_map hC hπ).symm
    _ = ((exponentialRace w).map raceDraw).map (cycleCountVector L) := by
      rw [luce_map_eq_raceDraw P w π hπ hMass]
    _ = (exponentialRace w).map (fun z => cycleCountVector L (raceDraw z)) :=
      Measure.map_map hC (measurable_raceDraw n)
    _ = _ := by simp only [cycleCountVector_raceDraw_eq_rank]

theorem luce_cycle_test_integral_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ, P.real {ω | π ω = σ} = w.mass σ)
    (L : ℕ) (F : (Fin L → ℕ) →ᵇ ℝ) :
    (∫ ω, F (cycleCountVector L (π ω)) ∂P) =
      ∫ z, F (cycleCountVector L (raceRankPermutation z)) ∂exponentialRace w := by
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hC : Measurable (cycleCountVector (n := n) L) := fun _ _ => trivial
  calc
    _ = ∫ x, F x ∂P.map (fun ω => cycleCountVector L (π ω)) :=
      (integral_map (hC.comp hπ).aemeasurable F.continuous.measurable.aestronglyMeasurable).symm
    _ = ∫ x, F x ∂(exponentialRace w).map
        (fun z => cycleCountVector L (raceRankPermutation z)) := by
      rw [luce_cycle_vector_map_eq P w π hπ hMass L]
    _ = _ := integral_map
      (measurable_race_permutation_statistic (cycleCountVector L)).aemeasurable
      F.continuous.measurable.aestronglyMeasurable

end Luce
