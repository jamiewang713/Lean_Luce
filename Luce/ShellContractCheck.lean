import Luce.Section4ShellTheorem
import Luce.ShellMigrationContract

noncomputable section
open Luce MeasureTheory
open scoped ENNReal

/-- This closed theorem has no external explicit, implicit, or instance
parameters. All allowed model data are quantified by the frozen contract. -/
theorem section4_contractCheck : ShellMigrationContract.section4 := by
  intro Ω mΩ P hP
  letI : ∀ n, MeasurableSpace (Ω n) := mΩ
  letI : ∀ n, IsProbabilityMeasure (P n) := hP
  intro w f hnorm hf hend π hπ hMass
  have h := Luce.Shell.section4_main_poisson_general Ω P w f hnorm hf hend π hπ hMass
  exact ⟨h.1, Luce.Shell.fullIntensity w f hnorm hf hend, rfl, h.2.1, h.2.2⟩

/-- The new constructor has exactly the same mathematical intensity as
the old constructor whenever the stronger uniform condition holds. -/
theorem Luce.Shell.fullIntensity_eq_uniform
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : UniformEndpointAssumption w) :
    Luce.Shell.fullIntensity w f hnorm hf hend.shell =
      Luce.fullIntensity w f hnorm hf hend := by
  rfl
