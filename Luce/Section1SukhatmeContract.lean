import Luce.Section1SukhatmeDefinitions

/-! A closed statement of Corollary 1.9, independent of its proof.
The decimal approximation to K_0(2) is illustrative; the exact identity is
included. No asymptotic estimate or profile condition is a hypothesis. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
universe u
namespace Luce.Sukhatme

def Corollary19 : Prop :=
  coefficient 0 = Real.exp (-1) ∧ coefficient 1 = besselK0 2 ∧
  ∀ (Ω : ℕ → Type u) (mΩ : ∀ n, MeasurableSpace (Ω n))
    (P : ∀ n, @Measure (Ω n) (mΩ n))
    (hP : ∀ n, @IsProbabilityMeasure (Ω n) (mΩ n) (P n)),
    letI : ∀ n, MeasurableSpace (Ω n) := mΩ
    letI : ∀ n, IsProbabilityMeasure (P n) := hP
    ∀ (π : ∀ n, Ω n → Equiv.Perm (Fin n)),
    (∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n)) →
    (∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (weights n).mass σ) →
    (∀ k : ℕ, 0 < coefficient k ∧
      Tendsto (fun n => (∫ ω, (Section5.cycleCount (π n ω) k : ℝ) ∂P n) /
        (coefficient k * Real.log n)) atTop (𝓝 1)) ∧
    (∀ L : ℕ, ∀ F : (Fin L → ℝ) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (normalizedCycleVector (π n ω) L) ∂P n)
        atTop (𝓝 (∫ z, F z ∂Section6.standardNormalVector (Fin L)))) ∧
    (∀ F : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (((Section5.cycleCount (π n ω) 0 : ℝ) -
        Real.exp (-1) * Real.log n) / Real.sqrt (Real.exp (-1) * Real.log n)) ∂P n)
        atTop (𝓝 (∫ z, F z ∂ProbabilityTheory.gaussianReal 0 1))) ∧
    (∀ (L J : ℕ) (a b : Fin J → ℝ),
      (∀ j, 0 < a j ∧ a j < b j ∧ b j < 1) →
      (Pairwise fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      (∀ (k : Fin L) (j : Fin J),
        Tendsto (fun n =>
          (∫ ω, (Section6.spatialCycleCount (π n ω) .right k.val (a j) (b j) : ℝ) ∂P n) /
            Real.log n) atTop (𝓝 (coefficient k.val * (b j - a j)))) ∧
      (∀ F : ((Fin L × Fin J) → ℝ) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, F (normalizedSpatialVector (π n ω) L J a b) ∂P n)
          atTop (𝓝 (∫ z, F z ∂Section6.standardNormalVector (Fin L × Fin J)))) ∧
      (∀ (k : Fin L) (j : Fin J) (delta : ℝ), 0 < delta →
        Tendsto (fun n => ∫ ω,
          (Section6.excursionCycleCount (π n ω) .right k.val (a j) (b j) delta : ℝ) ∂P n)
          atTop (𝓝 0)))

end Luce.Sukhatme
