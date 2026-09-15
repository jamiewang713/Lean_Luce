import Luce.Section4ShellMigrationContract

/-! A representation check, not a proof of the shell theorem. -/
open Luce MeasureTheory Set
namespace ShellMigrationContract

/-- The intensity specified in the frozen conclusion is exactly the existing
one whenever that existing constructor is available. No limiting law is changed. -/
theorem old_fullIntensity_underlying (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (hend : UniformEndpointAssumption w) :
    (fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1)) =
      (interiorDensityMeasure f 1).map (projIcc 0 1 zero_le_one) := rfl

end ShellMigrationContract
