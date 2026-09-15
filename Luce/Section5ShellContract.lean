import Luce.Section5ContractDefinitions

/-! Independent closed target for thm:short-cycles in the revised manuscript.
No implementation of that theorem is imported here. -/
noncomputable section
open Luce MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction ENNReal
universe u
namespace ShellMigrationContract

def section5 : Prop :=
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
    (∀ k : ℕ, Integrable (cycleTraceIntegrand f k) (cyclicProfileMeasure (k+1)) ∧
      0 ≤ cycleTraceIntensity f k) ∧
    ∀ L : ℕ,
      (∀ F : (Fin L → ℕ) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, F (cycleCountVector L (π n ω)) ∂P n) atTop
          (𝓝 (∫ z, F z ∂cycleVectorPoissonLaw f L))) ∧
      Tendsto (fun n => cycleVectorTotalVariation
        ((P n).map (fun ω => cycleCountVector L (π n ω))) (cycleVectorPoissonLaw f L))
        atTop (𝓝 0)

end ShellMigrationContract
