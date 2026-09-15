import Luce.Section5BlockIntegral

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce

/-- Every bulk joint falling-factorial moment has the independent-Poisson
value specified by the manuscript's literal truncated cycle intensities.
There is no endpoint, moment, boundedness, or integrability input. -/
theorem bulk_joint_factorial_moments (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (m : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell : Fin L, bulkCycleTraceIntensity f α ell.val ^ m ell)) := by
  classical
  by_cases hm : 0 < Fintype.card (Section5.CycleVertex L m)
  · have h := bulk_factorial_tendsto_canonical_block_integral w f hnorm hf L m hm α hα
    rw [canonical_block_integral_eq_intensity_product] at h
    exact h
  · have hz : m = fun _ => 0 := by
      funext ell
      by_contra h
      have hpos : 0 < m ell := Nat.pos_of_ne_zero h
      apply hm
      exact Fintype.card_pos_iff.mpr ⟨⟨⟨ell, ⟨0,hpos⟩⟩, ⟨0,Nat.succ_pos _⟩⟩⟩
    subst m
    simpa only [pow_zero, Finset.prod_const_one, bulk_factorial_expectation_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

/-- In particular the original expected bulk cycle count converges to the
literal truncated cyclic intensity. -/
theorem bulk_cycle_first_moment (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (k : ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z,
      (Section5.bulkCycleCount (raceRankPermutation z) α k : ℝ)
      ∂exponentialRace (w n)) atTop (𝓝 (bulkCycleTraceIntensity f α k)) := by
  have h := bulk_joint_factorial_moments w f hnorm hf (k+1)
    (fun ell => if ell = Fin.last k then 1 else 0) α hα
  simpa [apply_ite] using h

theorem bulk_cycle_trace_integrable {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (k : ℕ) {α : ℝ} (hα : α < 1) :
    IntegrableOn (cycleTraceIntegrand f k) (cyclicBulkCube (k+1) α) := by
  change IntegrableOn (fun x => ∏ a, cyclicProfileDensity f (x a)
    (x (finRotate (k+1) a))) (cyclicBulkCube (k+1) α)
  simpa only [one_mul] using
    hf.integrable_cyclic_density hα (finRotate (k+1))
      (g := fun _ => 1) continuousOn_const

theorem bulk_cycle_intensity_nonneg (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (k : ℕ) (α : ℝ) (hα : α < 1) :
    0 ≤ bulkCycleTraceIntensity f α k := by
  apply ge_of_tendsto (bulk_cycle_first_moment w f hnorm hf k α hα)
  exact Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => Nat.cast_nonneg _))

end Luce
