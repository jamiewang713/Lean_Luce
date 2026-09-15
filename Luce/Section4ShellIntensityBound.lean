import Luce.EndpointShellTightness
import Luce.Section4Intensity

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.Shell

theorem intensity_test_bound (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    ∀ η : ℝ, 0 < η → ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      ∀ β : ℝ, ∀ hβ : β < 1, ∀ g : Icc (0 : ℝ) 1 →ᵇ ℝ,
        (∀ x, 0 ≤ g x ∧ g x ≤ 1) → (∀ x, x.val ≤ a → g x = 0) →
        (∫ y, g y ∂(interiorIntensity w f hf β hβ : Measure (Icc (0 : ℝ) 1))) ≤ η := by
  intro η hη
  obtain ⟨a, ha0, ha1, hest⟩ := hend.expectation_tightness hnorm η hη
  refine ⟨a, ha0, ha1, ?_⟩
  intro β hβ g hg hs
  let A := fun n => ∫ e, ∫ y, g y
    ∂((interiorFixedPoints β (raceDraw e)).toFiniteMeasure : Measure (Icc (0 : ℝ) 1))
    ∂exponentialRace (w n)
  have hupper : ∀ᶠ n : ℕ in atTop, A n ≤ η := hest.mono fun n hn =>
    (integral_interior_observed_test_le_tail (w n) a β g hg hs).trans hn.le
  have hbounded : IsBoundedUnder (· ≤ ·) atTop A := ⟨η, hupper⟩
  apply (section4_interior_test_expectation_lower w f hnorm hf hβ g
    (fun x => (hg x).1) hbounded).trans
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n =>
    integral_nonneg (fun e => integral_nonneg (fun y => (hg y).1)))) hupper

theorem section4_interior_intensity_bounded
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    ∃ C : ℝ, ∀ β : ℝ, β < 1 → (interiorDensityMeasure f β).real univ ≤ C := by
  obtain ⟨a, _, ha, htest⟩ := intensity_test_bound w f hnorm hf hend 1 zero_lt_one
  let b := (a+1)/2
  have hab : a < b := by dsimp [b]; linarith
  have hb : b < 1 := by dsimp [b]; linarith
  refine ⟨(interiorDensityMeasure f b).real univ + 1, ?_⟩
  intro β hβ
  letI : IsFiniteMeasure (interiorDensityMeasure f β) := interiorDensityMeasure_finite hf hβ
  letI : IsFiniteMeasure (interiorDensityMeasure f b) := interiorDensityMeasure_finite hf hb
  have htail : (interiorDensityMeasure f β).real (Ioi b) ≤ 1 :=
    (interiorDensityMeasure_tail_le_test w f hf hab hβ).trans
      (htest β hβ (terminalIntensityTest a b)
        (terminalIntensityTest_bounds a b) (terminalIntensityTest_zero hab))
  have hleft : (interiorDensityMeasure f β).real (Iic b) ≤
      (interiorDensityMeasure f b).real univ := by
    have hμ : (interiorDensityMeasure f β).restrict (Iic b) ≤ interiorDensityMeasure f b := by
      rw [interiorDensityMeasure_restrict]
      exact interiorDensityMeasure_mono f (min_le_right _ _)
    have h := ENNReal.toReal_mono (measure_ne_top (interiorDensityMeasure f b) univ) (hμ univ)
    simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.real] using h
  have heq := measureReal_add_measureReal_compl (μ := interiorDensityMeasure f β)
    measurableSet_Iic (s := Iic b)
  rw [compl_Iic] at heq
  linarith

end Luce.Shell
