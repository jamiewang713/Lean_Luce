import Luce.Section6ContractDefinitions

/-! Independent closed Section 6 targets. These are propositions, not axioms
or claims of completed proofs. No implementation of the CLTs is imported. -/
noncomputable section
open Luce Luce.Section6 MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
universe u
namespace SampledProfileContract

def powerLaw (grid : SamplingGrid) : Prop :=
  ∀ (Ω : ℕ → Type u) (mΩ : ∀ n, MeasurableSpace (Ω n))
    (P : ∀ n, @Measure (Ω n) (mΩ n))
    (hP : ∀ n, @IsProbabilityMeasure (Ω n) (mΩ n) (P n)),
    letI : ∀ n, MeasurableSpace (Ω n) := mΩ
    letI : ∀ n, IsProbabilityMeasure (P n) := hP
    ∀ (w : WeightArray) (f : ℝ → ℝ) (left right : EndpointBehavior),
    SampledRates grid w f → PowerProfile f left right →
    ∀ (π : ∀ n, Ω n → Equiv.Perm (Fin n)),
    (∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n)) →
    (∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) →
    (∀ k : ℕ, 0 < totalCoefficient left right k ∧
      Tendsto (fun n => (∫ ω, (Section5.cycleCount (π n ω) k : ℝ) ∂P n) /
        (totalCoefficient left right k * Real.log n)) atTop (𝓝 1)) ∧
    ∀ L : ℕ, ∀ F : (Fin L → ℝ) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (normalizedCycleVector (π n ω) left right L) ∂P n)
        atTop (𝓝 (∫ z, F z ∂standardNormalVector (Fin L)))

def spatial (grid : SamplingGrid) : Prop :=
  ∀ (Ω : ℕ → Type u) (mΩ : ∀ n, MeasurableSpace (Ω n))
    (P : ∀ n, @Measure (Ω n) (mΩ n))
    (hP : ∀ n, @IsProbabilityMeasure (Ω n) (mΩ n) (P n)),
    letI : ∀ n, MeasurableSpace (Ω n) := mΩ
    letI : ∀ n, IsProbabilityMeasure (P n) := hP
    ∀ (w : WeightArray) (f : ℝ → ℝ) (left right : EndpointBehavior),
    SampledRates grid w f → PowerProfile f left right →
    ∀ (π : ∀ n, Ω n → Equiv.Perm (Fin n)),
    (∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n)) →
    (∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) →
    ∀ (L J : ℕ) (a b : Fin J → ℝ),
    (∀ j, 0 < a j ∧ a j < b j ∧ b j < 1) →
    (Pairwise fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
    (∀ z : SpatialIndex left right L J,
      0 < cornerCoefficient z.1.val (cornerBehavior left right z.1.val) z.2.1.val ∧
      Tendsto (fun n =>
        (∫ ω, (spatialCycleCount (π n ω) z.1.val z.2.1.val (a z.2.2) (b z.2.2) : ℝ) ∂P n) /
          Real.log n) atTop
        (𝓝 (cornerCoefficient z.1.val (cornerBehavior left right z.1.val) z.2.1.val *
          (b z.2.2 - a z.2.2)))) ∧
    (∀ F : (SpatialIndex left right L J → ℝ) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (normalizedSpatialVector (π n ω) left right L J a b) ∂P n)
        atTop (𝓝 (∫ z, F z ∂standardNormalVector (SpatialIndex left right L J)))) ∧
    (∀ (z : SpatialIndex left right L J) (delta : ℝ), 0 < delta →
      Tendsto (fun n => ∫ ω,
        (excursionCycleCount (π n ω) z.1.val z.2.1.val (a z.2.2) (b z.2.2) delta : ℝ) ∂P n)
        atTop (𝓝 0))

def critical (grid : SamplingGrid) : Prop :=
  ∀ (Ω : ℕ → Type u) (mΩ : ∀ n, MeasurableSpace (Ω n))
    (P : ∀ n, @Measure (Ω n) (mΩ n))
    (hP : ∀ n, @IsProbabilityMeasure (Ω n) (mΩ n) (P n)),
    letI : ∀ n, MeasurableSpace (Ω n) := mΩ
    letI : ∀ n, IsProbabilityMeasure (P n) := hP
    ∀ (w : WeightArray) (f : ℝ → ℝ) (c eta rightLimit : ℝ),
    SampledRates grid w f → CriticalProfile f c eta rightLimit →
    ∀ (π : ∀ n, Ω n → Equiv.Perm (Fin n)),
    (∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n)) →
    (∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) →
    (∀ F : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (((Section5.cycleCount (π n ω) 0 : ℝ) -
        Real.log (Real.log n)) / Real.sqrt (Real.log (Real.log n))) ∂P n)
        atTop (𝓝 (∫ z, F z ∂ProbabilityTheory.gaussianReal 0 1))) ∧
    Tendsto (fun n => (∫ ω, (Section5.cycleCount (π n ω) 0 : ℝ) ∂P n) /
      Real.log (Real.log n)) atTop (𝓝 1) ∧
    (∀ k : ℕ, ∃ C : ℝ, ∀ n,
      (∫ ω, (Section5.cycleCount (π n ω) (k+1) : ℝ) ∂P n) ≤ C)

/-- Both original sampling and the full interior-grid extension. -/
def section6 : Prop :=
  powerLaw.{u} .midpoint ∧ spatial.{u} .midpoint ∧ critical.{u} .midpoint ∧
    powerLaw.{u} .interior ∧ spatial.{u} .interior ∧ critical.{u} .interior

end SampledProfileContract
