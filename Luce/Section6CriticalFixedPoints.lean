import Luce.Section6CriticalReferenceBounds
import Luce.BernoulliReferenceMean
import Luce.Section3LuceLaw

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace Luce.Section6

theorem critical_loglog_tendsto :
    Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- The fixed-point normal limit and mean asymptotic for the exponential
race, with no quantile or compensator assumptions added to the profile. -/
theorem CriticalProfile.fixed_point_race_limits {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) (grid : SamplingGrid) (w : WeightArray)
    (hw : SampledRates grid w f) :
    (∀ F : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ e, F (((Section5.cycleCount (raceRankPermutation e) 0 : ℝ)-
        Real.log (Real.log n))/Real.sqrt (Real.log (Real.log n))) ∂exponentialRace (w n))
        atTop (𝓝 (∫ z, F z ∂ProbabilityTheory.gaussianReal 0 1))) ∧
    Tendsto (fun n => (∫ e, (Section5.cycleCount (raceRankPermutation e) 0 : ℝ)
      ∂exponentialRace (w n))/Real.log (Real.log n)) atTop (𝓝 1) := by
  obtain ⟨eps,C,heps,heps1,hC,hrows⟩ := hp.reference_rows
  have hh := hrows grid w hw
  let q := fun n => criticalReference n (criticalLower n) (criticalUpper eps n)
  let X := fun n => (raceInteriorBernoulli (w n) 1).toProcess
  constructor
  · intro F
    have h := BernoulliCLT.boundedContinuous_tendsto_of_eventual_reference
      (fun n => exponentialRace (w n)) X id q critical_loglog_tendsto
      (hh.mono fun _ hn => hn.1) (hh.mono fun _ hn => hn.2) F
    simpa only [X,id_eq,critical_full_count] using h
  · have h := BernoulliCLT.mean_tendsto_of_reference
      (fun n => exponentialRace (w n)) X id q critical_loglog_tendsto
      (hh.mono fun _ hn => ⟨hn.2.1,hn.2.2.1⟩)
    simpa only [X,id_eq,critical_full_count] using h

/-- Transfer any real statistic of one cycle count from the exponential
race to a measurable permutation with the same full Luce masses. -/
theorem luce_cycle_statistic_integral_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ, P.real {ω | π ω = σ} = w.mass σ) (k : ℕ) (H : ℕ → ℝ) :
    (∫ ω, H (Section5.cycleCount (π ω) k) ∂P) =
      ∫ e, H (Section5.cycleCount (raceRankPermutation e) k) ∂exponentialRace w := by
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hH : Measurable (fun σ : Equiv.Perm (Fin n) => H (Section5.cycleCount σ k)) :=
    fun _ _ => trivial
  calc
    _ = ∫ σ, H (Section5.cycleCount σ k) ∂P.map π :=
      (integral_map hπ.aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ σ, H (Section5.cycleCount σ k) ∂(exponentialRace w).map raceDraw := by
      rw [luce_map_eq_raceDraw P w π hπ hMass]
    _ = ∫ e, H (Section5.cycleCount (raceDraw e) k) ∂exponentialRace w :=
      integral_map (measurable_raceDraw n).aemeasurable hH.aestronglyMeasurable
    _ = _ := by simp only [critical_raceDraw_eq_rank_symm,Section5.cycleCount_symm]

theorem CriticalProfile.fixed_point_limits
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {f : ℝ → ℝ} {c eta d : ℝ} (hp : CriticalProfile f c eta d)
    (grid : SamplingGrid) (w : WeightArray) (hw : SampledRates grid w f)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) _ ⊤ (π n))
    (hMass : ∀ n σ, (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    (∀ F : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (((Section5.cycleCount (π n ω) 0 : ℝ)-Real.log (Real.log n))/
        Real.sqrt (Real.log (Real.log n))) ∂P n)
        atTop (𝓝 (∫ z, F z ∂ProbabilityTheory.gaussianReal 0 1))) ∧
    Tendsto (fun n => (∫ ω, (Section5.cycleCount (π n ω) 0 : ℝ) ∂P n)/
      Real.log (Real.log n)) atTop (𝓝 1) := by
  obtain ⟨hclt,hmean⟩ := hp.fixed_point_race_limits grid w hw
  constructor
  · intro F
    have he (n : ℕ) := luce_cycle_statistic_integral_eq (P n) (w n) (π n) (hπ n) (hMass n) 0
      (fun x => F (((x : ℝ)-Real.log (Real.log n))/Real.sqrt (Real.log (Real.log n))))
    simp_rw [he]
    exact hclt F
  · have he (n : ℕ) := luce_cycle_statistic_integral_eq (P n) (w n) (π n) (hπ n) (hMass n) 0
      (fun x => (x : ℝ))
    simp_rw [he]
    exact hmean

end Luce.Section6
