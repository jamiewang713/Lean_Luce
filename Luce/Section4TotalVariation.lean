import Luce.Section4FullIntensity
import Luce.Section4CountLaw
import Luce.Section4Count
import Luce.Section4DiscreteTotalVariation
import Luce.Section4Poisson

/-! # The total-variation Poisson limit for the number of fixed points

Source: `fixed_points.tex:155–159,958–961`, `eq:count-poisson`.
The total count is the number of actual fixed labels. Its law is a probability
measure, and total variation uses the supremum over event probabilities.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

namespace Luce

/-- The manuscript's random variable `X_n`, extracted from its literal point measure. -/
def fixedPointCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (fixedPoints π).count univ

/-- The total-mass representation counts exactly the fixed labels, with no
inverse-permutation or endpoint discrepancy. The statement also covers `n = 0`. -/
theorem fixedPointCount_eq_card {n : ℕ} (π : Equiv.Perm (Fin n)) :
    fixedPointCount π = (Finset.univ.filter fun k => π k = k).card := by
  classical
  rw [fixedPointCount, fixedPoints, interiorFixedPoints,
    observedPointMeasure_count _ _ MeasurableSet.univ]
  apply congrArg Finset.card
  ext k
  have hk : ((k.val : ℝ) + 1) / n ≤ 1 := (section3Location n k).property.2
  simp only [Finset.mem_filter, Finset.mem_univ, decide_eq_true_eq, mem_univ,
    and_true, inverse_fixed_iff, hk, true_and]

/-- Fixed-point measures are measurable on the finite discrete permutation space. -/
theorem measurable_fixedPoints (n : ℕ) :
    @Measurable (Equiv.Perm (Fin n)) (FinitePointMeasure (Icc (0 : ℝ) 1)) ⊤
      inferInstance fixedPoints := fun _ _ => trivial

/-- The actual total-count distribution on an arbitrary row probability space. -/
def fixedPointCountLaw {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π) : ProbabilityMeasure ℕ :=
  ⟨P.map (fun ω => fixedPointCount (π ω)), P.isProbabilityMeasure_map
    ((FinitePointMeasure.measurable_count MeasurableSet.univ).comp
      ((measurable_fixedPoints n).comp hπ)).aemeasurable⟩

/-- The canonical exponential-race realization of the fixed-point count law. -/
def raceFixedPointCountLaw {n : ℕ} (w : Weights n) : ProbabilityMeasure ℕ :=
  fixedPointCountLaw (exponentialRace w) raceDraw (measurable_raceDraw n)

/-- The standard scalar Poisson law, with its proved probability normalization. -/
def poissonProbabilityMeasure (r : ℝ≥0) : ProbabilityMeasure ℕ :=
  ⟨poissonMeasure r, inferInstance⟩

/-- The generic final passage of Section 4: the proved spatial limit gives
pointwise count probabilities, then the discrete Scheffé theorem gives TV.
The manuscript-specific theorems below discharge the spatial premise. -/
theorem fixedPointCountLaw_totalVariation_of_pointProcess
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (ν : FiniteMeasure (Icc (0 : ℝ) 1))
    (hWeak : ∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw ν))) :
    Tendsto (fun n => probabilityTotalVariation
      (fixedPointCountLaw (P n) (π n) (hπ n)) (poissonProbabilityMeasure ν.mass))
      atTop (𝓝 0) := by
  apply tendsto_probabilityTotalVariation_of_singletons
  intro k
  exact pointMeasure_random_count_singleton_poisson_tendsto Ω P
    (fun n ω => fixedPoints (π n ω))
    (fun n => (measurable_fixedPoints n).comp (hπ n)) ν hWeak k

/-- The scalar Poisson parameter is exactly the manuscript's Lebesgue
integral. Taking its nonnegative subtype does not truncate any negative value. -/
theorem fullIntensity_mass_eq_toNNReal_integral
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    (fullIntensity w f hnorm hf hend).mass =
      Real.toNNReal (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x) := by
  rw [← fullIntensity_mass w f hnorm hf hend]
  simp

/-- Equation `eq:count-poisson`: the full count law converges in probability
total variation to Poisson with the literal diagonal integral as parameter. -/
theorem section4_count_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
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
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
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

end Luce
