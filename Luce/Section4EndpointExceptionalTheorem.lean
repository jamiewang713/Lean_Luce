import Luce.Section4EndpointExceptional
import Luce.Section4EndpointTailPoisson

/-! Closed statements of Corollary 4.7 of `fixed_points_sampled_profile.tex`.
The exceptional-shell condition replaces the original endpoint assumption
throughout, including in the construction of the finite Poisson intensity. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce

/-- The two endpoint conclusions of Corollary 4.7 require normalization
and the raw combined cost condition, without a profile assumption. -/
theorem corollary47_endpoint (w : WeightArray) (E : ∀ n, Finset (Fin n))
    (hnorm : NormalizedWeights w) (hend : EndpointExceptionalAssumption w E) :
    Tendsto (fun J : ℕ => limsup (fun n => terminalDepthExpectation w n J) atTop)
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun α : ℝ => limsup (fun n : ℕ =>
      ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace (w n)) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  constructor
  · exact real_iterated_limit_of_ennreal _
      (fun _ _ => integral_nonneg (fun _ => Nat.cast_nonneg _))
      (hend.terminal_depth_limit hnorm)
  · exact (hend.expectation_tightness hnorm).expectation_limit

/-- Equation `eq:shell-tail-epsilon` with the manuscript's `ε ↓ 0`
parameter and strict spatial cutoff `k > (1-ε)n`. -/
theorem corollary47_epsilon (w : WeightArray) (E : ∀ n, Finset (Fin n))
    (hnorm : NormalizedWeights w) (hend : EndpointExceptionalAssumption w E) :
    Tendsto (fun ε : ℝ => limsup (fun n : ℕ =>
      ∫ e, (tailFixedPointCount e (1-ε) : ℝ) ∂exponentialRace (w n)) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hc : Tendsto (fun ε : ℝ => 1-ε) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_zero, id_eq] using tendsto_const_nhds.sub
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 1-ε < 1
      have hε' : 0 < ε := hε
      linarith
  exact (corollary47_endpoint w E hnorm hend).2.comp hc

/-- The full intensity is the diagonal density proved finite using the
exceptional-shell condition. No finiteness witness is an extra hypothesis. -/
def exceptionalFullIntensity (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Finset (Fin n)) (hend : EndpointExceptionalAssumption w E) :
    FiniteMeasure (Icc (0 : ℝ) 1) :=
  EndpointTail.fullIntensity w f hnorm hf (hend.expectation_tightness hnorm)

theorem exceptionalFullIntensity_projection (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Finset (Fin n)) (hend : EndpointExceptionalAssumption w E) :
    (exceptionalFullIntensity w f hnorm hf E hend : Measure (Icc (0 : ℝ) 1)).map Subtype.val =
      interiorDensityMeasure f 1 :=
  EndpointTail.fullIntensity_projection_recovery w f hnorm hf (hend.expectation_tightness hnorm)

/-- Corollary 4.7's consequence for Theorem 1.3: integrable diagonal
intensity, weak convergence of the entire point process, and convergence of
the full count in total variation, under `eq:exceptional-shell-condition`. -/
theorem corollary47 (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Finset (Fin n)) (hend : EndpointExceptionalAssumption w E) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (exceptionalFullIntensity w f hnorm hf E hend)))) ∧
    Tendsto (fun n => probabilityTotalVariation (raceFixedPointCountLaw (w n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0) :=
  EndpointTail.section4_main_poisson w f hnorm hf (hend.expectation_tightness hnorm)

/-- The same conclusion for arbitrary measurable Luce permutations on
varying row probability spaces; their defining finite masses suffice. -/
theorem corollary47_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Finset (Fin n)) (hend : EndpointExceptionalAssumption w E)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (exceptionalFullIntensity w f hnorm hf E hend)))) ∧
    Tendsto (fun n => probabilityTotalVariation (fixedPointCountLaw (P n) (π n) (hπ n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0) :=
  EndpointTail.section4_main_poisson_general Ω P w f hnorm hf
    (hend.expectation_tightness hnorm) π hπ hMass

end Luce
