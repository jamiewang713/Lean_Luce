import Luce.Section4EndpointShellDefinitions
import Luce.Section4TotalVariation

/-! Frozen Section 4 target, before implementing any generalized main proof.
This module does not import the generalized implementation. The existential
finite intensity is a CONCLUSION, with its underlying measure fixed exactly.
The existing `fullIntensity` cannot be used here because it takes the old
uniform endpoint proof as an argument. -/

noncomputable section
open Luce MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ENNReal
universe u
namespace ShellMigrationContract

/-- Closed arbitrary-space form of `thm:main-poisson`, source lines 318–332.
There are no ambient mathematical section variables or assumed instances. -/
def section4 : Prop :=
  ∀ (Ω : ℕ → Type u) (mΩ : ∀ n, MeasurableSpace (Ω n))
    (P : ∀ n, @Measure (Ω n) (mΩ n)),
    ∀ (hP : ∀ n, @IsProbabilityMeasure (Ω n) (mΩ n) (P n)),
    letI : ∀ n, MeasurableSpace (Ω n) := mΩ
    letI : ∀ n, IsProbabilityMeasure (P n) := hP
    ∀ (w : WeightArray) (f : ℝ → ℝ),
    NormalizedWeights w → ProfileLimit w f →
    Tendsto (fun J : ℕ => limsup (fun n : ℕ =>
      ∑' j : ℕ, if J ≤ j then shellCost w n j else 0) atTop)
      atTop (𝓝 (0 : ℝ≥0∞)) →
    ∀ (π : ∀ n, Ω n → Equiv.Perm (Fin n))
      (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n)),
    (∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) →
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    ∃ ν : FiniteMeasure (Icc (0 : ℝ) 1),
      (ν : Measure (Icc (0 : ℝ) 1)) =
        (interiorDensityMeasure f 1).map (projIcc 0 1 zero_le_one) ∧
      (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
          (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw ν))) ∧
      Tendsto (fun n => probabilityTotalVariation (fixedPointCountLaw (P n) (π n) (hπ n))
          (poissonProbabilityMeasure (Real.toNNReal
            (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0)

end ShellMigrationContract
