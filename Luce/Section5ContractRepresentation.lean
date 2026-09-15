import Luce.Section5ContractDefinitions

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce

/-- The profile product measure is precisely Lebesgue measure on the
closed unit cube, since its boundary has measure zero. No profile assumption
is needed for this representation equality. -/
theorem cyclicProfileMeasure_eq_closed_cube (r : ℕ) :
    cyclicProfileMeasure r = volume.restrict (cyclicBulkCube r 1) := by
  unfold cyclicProfileMeasure cyclicBulkCube
  change Measure.pi (fun _ : Fin r => profileMeasure) =
    (Measure.pi (fun _ : Fin r => (volume : Measure ℝ))).restrict _
  rw [Measure.restrict_pi_pi]
  congr 1
  funext a
  exact Measure.restrict_congr_set Ioo_ae_eq_Icc

theorem cycleTraceIntensity_eq_manuscript (f : ℝ → ℝ) (k : ℕ) :
    cycleTraceIntensity f k = (1/(k+1 : ℝ)) *
      ∫ x in cyclicBulkCube (k+1) 1,
        ∏ a, cyclicProfileDensity f (x a) (x (finRotate (k+1) a)) := by
  rw [cycleTraceIntensity, cyclicProfileMeasure_eq_closed_cube]
  rfl

instance cycleVectorPoissonLaw_probability (f : ℝ → ℝ) (L : ℕ) :
    IsProbabilityMeasure (cycleVectorPoissonLaw f L) := by
  unfold cycleVectorPoissonLaw
  infer_instance

theorem cycleCountVector_apply {n : ℕ} (L : ℕ) (R : Equiv.Perm (Fin n)) (k : Fin L) :
    cycleCountVector L R k = Section5.cycleCount R k.val := rfl

end Luce
