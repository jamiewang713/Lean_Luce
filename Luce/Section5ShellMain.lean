import Luce.Section5LuceTransfer

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace Luce

/-- The complete revised Section 5 conclusion on every realization of the
finite Luce law, with exactly the manuscript's model assumptions. -/
theorem section5_main_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    (∀ k : ℕ, Integrable (cycleTraceIntegrand f k) (cyclicProfileMeasure (k+1)) ∧
      0 ≤ cycleTraceIntensity f k) ∧
    ∀ L : ℕ,
      (∀ F : (Fin L → ℕ) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, F (cycleCountVector L (π n ω)) ∂P n) atTop
          (𝓝 (∫ z, F z ∂cycleVectorPoissonLaw f L))) ∧
      Tendsto (fun n => cycleVectorTotalVariation
        ((P n).map (fun ω => cycleCountVector L (π n ω))) (cycleVectorPoissonLaw f L))
        atTop (𝓝 0) := by
  refine ⟨fun k => ⟨hend.cycle_trace_integrable hnorm hf k, cycle_intensity_nonneg hf k⟩,
    fun L => ⟨?_, ?_⟩⟩
  · intro F
    simp_rw [luce_cycle_test_integral_eq (P _) (w _) (π _) (hπ _) (hMass _) L F]
    exact hend.cycle_vector_weak hnorm hf L F
  · simp_rw [luce_cycle_vector_map_eq (P _) (w _) (π _) (hπ _) (hMass _) L]
    exact hend.cycle_vector_totalVariation hnorm hf L

end Luce
