import Luce.Section4ShellTotalVariation

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.Shell

theorem section4_main_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))) ∧
    Tendsto (fun n => probabilityTotalVariation (raceFixedPointCountLaw (w n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0) :=
  ⟨section4_profileDiagonal_integrable w f hnorm hf hend,
    section4_full_poisson w f hnorm hf hend,
    section4_count_poisson w f hnorm hf hend⟩

/-- The same complete theorem for arbitrary row probability spaces and
measurable Luce permutations with the manuscript's exact finite masses.
Cross-row independence, regularity of the profile beyond L¹ convergence,
and global upper/lower rate bounds are not hypotheses. -/
theorem section4_main_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))) ∧
    Tendsto (fun n => probabilityTotalVariation (fixedPointCountLaw (P n) (π n) (hπ n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0) :=
  ⟨section4_profileDiagonal_integrable w f hnorm hf hend,
    section4_full_poisson_general Ω P w f hnorm hf hend π hπ hMass,
    section4_count_poisson_general Ω P w f hnorm hf hend π hπ hMass⟩

end Luce.Shell
