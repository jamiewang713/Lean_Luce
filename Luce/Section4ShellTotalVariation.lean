import Luce.Section4ShellPoisson
import Luce.Section4TotalVariation

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.Shell

theorem fullIntensity_mass_eq_toNNReal_integral
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    (fullIntensity w f hnorm hf hend).mass =
      Real.toNNReal (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x) := by
  rw [← fullIntensity_mass w f hnorm hf hend]
  simp

/-- Equation `eq:count-poisson`: the full count law converges in probability
total variation to Poisson with the literal diagonal integral as parameter. -/
theorem section4_count_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    Tendsto (fun n => probabilityTotalVariation (raceFixedPointCountLaw (w n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0) := by
  have h := fixedPointCountLaw_totalVariation_of_pointProcess (fun n => Fin n → ℝ)
    (fun n => exponentialRace (w n)) (fun _ => raceDraw) (fun n => measurable_raceDraw n)
    (fullIntensity w f hnorm hf hend) (section4_full_poisson w f hnorm hf hend)
  rw [fullIntensity_mass_eq_toNNReal_integral w f hnorm hf hend] at h
  exact h

/-- The total-variation conclusion for arbitrary realizations of the Luce
law, with only its defining finite masses and the manuscript assumptions. -/
theorem section4_count_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    Tendsto (fun n => probabilityTotalVariation
      (fixedPointCountLaw (P n) (π n) (hπ n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0) := by
  have h := fixedPointCountLaw_totalVariation_of_pointProcess Ω P π hπ
    (fullIntensity w f hnorm hf hend)
    (section4_full_poisson_general Ω P w f hnorm hf hend π hπ hMass)
  rw [fullIntensity_mass_eq_toNNReal_integral w f hnorm hf hend] at h
  exact h

end Luce.Shell
