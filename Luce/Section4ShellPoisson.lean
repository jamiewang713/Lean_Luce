import Luce.Section4Approximation
import Luce.Section4ShellFullIntensity
import Luce.LaplaceCountTightness

/-! # The full fixed-point process in Section 4

Source: `fixed_points.tex:953–956`, concluding `thm:main-poisson`.
The terminal approximation is discharged by the proved endpoint theorem;
the limiting intensity is the actual finite full diagonal density.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

namespace Luce.Shell

/-- The full process has the Poisson Laplace limit, under exactly the
normalized model and the paper's profile and endpoint assumptions. -/
theorem section4_full_laplace
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
    Tendsto (fun n => ∫ e, pointLaplace (fun x => (g x : ℝ))
      (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (fullIntensity w f hnorm hf hend))) := by
  let v := fun α n => ∫ e, pointLaplace (fun x => (g x : ℝ))
    (interiorFixedPoints α (raceDraw e)) ∂exponentialRace (w n)
  let a := fun α : ℝ => if hα : α < 1 then
    ∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
      ∂finitePoissonLaw (interiorIntensity w f hf α hα)
    else ∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
      ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)
  let p := fun α n => (exponentialRace (w n)).real {e | 0 < tailFixedPointCount e α}
  have hp (α : ℝ) : IsBoundedUnder (· ≤ ·) atTop (p α) :=
    ⟨1, show ∀ᶠ n : ℕ in atTop, p α n ≤ 1 from
      Eventually.of_forall fun _ => measureReal_le_one⟩
  have htail : Tendsto (fun α => limsup (p α) atTop) (𝓝[<] (1 : ℝ)) (𝓝 0) :=
    hend.probability_tightness hnorm
  apply tendsto_of_terminal_approximation _ v a p _ hp htail
    (tendsto_laplace_finitePoissonLaw_interior_full w f hnorm hf hend g)
  · intro α hα
    have h := pointMeasure_laplace_of_integrals (fun n => exponentialRace (w n))
      (fun n => raceInteriorBernoulli (w n) α) section3Location
      (interiorIntensity w f hf α hα)
      (section3_predictable_tests w f hnorm hf hα)
      (section3_predictable_maximum w f hnorm hf hα) g
    simpa only [raceInteriorBernoulli_pointMeasure, a, dif_pos hα] using h
  · intro α _ n
    exact section4_laplace_cutoff_error (w n) α g

/-- Equation `eq:point-process-limit`: convergence of the actual full
finite point measure in its weak topology. Every bounded continuous test
of the point measure is allowed, and all approximation and tightness
conditions have been proved from the model assumptions. -/
theorem section4_full_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend))) := by
  let μ : ℕ → Measure (FinitePointMeasure (Icc (0 : ℝ) 1)) :=
    fun n => (exponentialRace (w n)).map (fun e => fixedPoints (raceDraw e))
  let Q := finitePoissonLaw (fullIntensity w f hnorm hf hend)
  have hΞ (n : ℕ) : Measurable (fun e : Fin n → ℝ => fixedPoints (raceDraw e)) :=
    measurable_interiorFixedPoints_race (w n) 1
  haveI (n : ℕ) : IsProbabilityMeasure (μ n) :=
    Measure.isProbabilityMeasure_map (hΞ n).aemeasurable
  have hLaplace (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
      Tendsto (fun n => ∫ ξ, momentLaplace g (pointMoment ξ) ∂μ n) atTop
        (𝓝 (∫ ξ, momentLaplace g (pointMoment ξ) ∂Q)) := by
    simp_rw [momentLaplace_pointMoment_eq_pointLaplace]
    have hg := (NNReal.continuous_coe.comp g.continuous).measurable
    have heq (n : ℕ) : (∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ ∂μ n) =
        ∫ e, pointLaplace (fun x => (g x : ℝ)) (fixedPoints (raceDraw e))
          ∂exponentialRace (w n) :=
      integral_map_of_stronglyMeasurable (hΞ n)
        (measurable_pointLaplace _ hg (fun x => (g x).coe_nonneg)).stronglyMeasurable
    simp_rw [heq]
    exact section4_full_laplace w f hnorm hf hend g
  have h := pointMeasure_law_convergence_of_laplace μ Q hLaplace
    (pointMeasure_tightness_of_laplace μ Q hLaplace) F
  have heq (n : ℕ) : (∫ ξ, F ξ ∂μ n) =
      ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n) :=
    integral_map_of_stronglyMeasurable (hΞ n)
      (measurable_boundedContinuous_pointMeasure F).stronglyMeasurable
  simpa only [heq] using h

/-- The full point-process limit for every Luce permutation realization.
The row masses are precisely `eq:luce-law`; no coupling between rows or
asymptotic hypothesis beyond the manuscript assumptions is required. -/
theorem section4_full_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ)
    (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend))) := by
  have heq (n : ℕ) : (∫ ω, F (fixedPoints (π n ω)) ∂P n) =
      ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n) := by
    letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
    have htest : Measurable (fun σ : Equiv.Perm (Fin n) => F (fixedPoints σ)) :=
      fun _ _ => trivial
    calc
      _ = ∫ σ, F (fixedPoints σ) ∂(P n).map (π n) :=
        (integral_map_of_stronglyMeasurable (hπ n) htest.stronglyMeasurable).symm
      _ = ∫ σ, F (fixedPoints σ) ∂(exponentialRace (w n)).map raceDraw := by
        rw [luce_map_eq_raceDraw (P n) (w n) (π n) (hπ n) (hMass n)]
      _ = _ := integral_map_of_stronglyMeasurable (measurable_raceDraw n) htest.stronglyMeasurable
  simpa only [heq] using section4_full_poisson w f hnorm hf hend F

end Luce.Shell
