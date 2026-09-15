import Luce.Section65InverseCycleStatistics
import Luce.Section3LuceLaw

noncomputable section
open MeasureTheory
namespace Luce.Section6

theorem invariant_statistic_raceDraw_eq_rank65 {n : ℕ}
    (G : Equiv.Perm (Fin n) → ℝ) (hG : ∀ R, G R.symm = G R) (z : Fin n → ℝ) :
    G (raceDraw z) = G (raceRankPermutation z) := by
  classical
  by_cases h : Function.Injective z
  · simp only [raceDraw_eq z h, raceRankPermutation_eq z h, drawPermutation, hG]
  · simp only [raceDraw,raceRankPermutation,h,dite_false]

/-- Transfer any inverse-invariant real cycle statistic to any realization
of the original finite Luce law, on an arbitrary probability space. -/
theorem luce_invariant_integral_eq65 {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ, P.real {ω | π ω = σ} = w.mass σ)
    (G : Equiv.Perm (Fin n) → ℝ) (hG : ∀ R, G R.symm = G R) :
    (∫ ω, G (π ω) ∂P) = ∫ z, G (raceRankPermutation z) ∂exponentialRace w := by
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hm : Measurable G := fun _ _ => trivial
  calc
    _ = ∫ R, G R ∂P.map π := (integral_map hπ.aemeasurable hm.aestronglyMeasurable).symm
    _ = ∫ R, G R ∂(exponentialRace w).map raceDraw := by
      rw [luce_map_eq_raceDraw P w π hπ hMass]
    _ = ∫ z, G (raceDraw z) ∂exponentialRace w :=
      integral_map (measurable_raceDraw n).aemeasurable hm.aestronglyMeasurable
    _ = _ := by simp only [invariant_statistic_raceDraw_eq_rank65 G hG]

end Luce.Section6
