import Luce.Section4TotalVariation
import Luce.Section3Representations

/-! # Theorem 1.3, proved in Section 4

Source: `fixed_points.tex:264–278,923–961`. This entry point packages the
completed dependency chain: finite diagonal intensity, convergence of the
full fixed-point measure, and total variation convergence of its count.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

namespace Luce

/-- The full process, mapped to the real line, is literally `eq:fixed-process`. -/
theorem fixedPoints_realMeasure {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ((fixedPoints π).toFiniteMeasure : Measure (Icc (0 : ℝ) 1)).map Subtype.val =
      ∑ k : Fin n, if π.symm k = k then
        Measure.dirac (((k.val : ℝ) + 1) / n) else 0 := by
  classical
  rw [fixedPoints, interiorFixedPoints_realMeasure]
  apply Finset.sum_congr rfl
  intro k _
  have hk : ((k.val : ℝ) + 1) / n ≤ 1 := (section3Location n k).property.2
  simp only [hk, true_and]

/-- The real parameter used by the scalar Poisson law is nonnegative. -/
theorem section4_lambda_nonneg
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    0 ≤ ∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x := by
  rw [← fullIntensity_mass w f hnorm hf hend]
  exact (fullIntensity w f hnorm hf hend).mass.coe_nonneg

/-- The full conclusion of Theorem `thm:main-poisson`, in the canonical
independent exponential-clock model. No missing estimate or convergence
statement is assumed. Every bounded weak-continuous point-measure test is
quantified, and the count conclusion uses the exact probability-TV convention. -/
theorem section4_main_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
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
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
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

end Luce
