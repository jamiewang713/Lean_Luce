import Luce.Section5PointCutoff

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators Topology
namespace Luce

/-- Full cycle-count point probabilities, after the manuscript's endpoint
cutoff removal. The shell assumption supplies expectation tightness through
its proved theorem, not through an additional hypothesis. -/
theorem EndpointShellAssumption.cycle_point_indicator_limit
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) :
    Tendsto (fun n => ∫ z,
      (if cycleCountVector L (raceRankPermutation z) = q then (1 : ℝ) else 0)
      ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell, Real.exp (-cycleTraceIntensity f ell.val) *
        cycleTraceIntensity f ell.val ^ q ell / ((q ell).factorial : ℝ))) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨β, hβ, htail⟩ := hend.short_cycle_tail_small hnorm hf L (ε := ε/3) (by positivity)
  have hnear : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), β < α :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hβ)
  have hform := Metric.tendsto_nhds.mp (hend.cycle_point_formula_tendsto hnorm hf L q)
    (ε/3) (by positivity)
  have hleft : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), α < 1 := self_mem_nhdsWithin
  obtain ⟨α, ⟨hα, hβα⟩, hclose⟩ := ((hleft.and hnear).and hform).exists
  have hbulk := Metric.tendsto_nhds.mp
    (bulk_cycle_point_indicator_limit w f hnorm hf L q α hα) (ε/3) (by positivity)
  filter_upwards [htail, hbulk] with n hn hnB
  have he := (cycle_point_indicator_cutoff_error w L n q α).trans
    (shortCycleTailExpectation_antitone w L n hβα.le)
  rw [Real.dist_eq] at hclose hnB ⊢
  have ht := abs_sub_le
    (∫ z, (if cycleCountVector L (raceRankPermutation z) = q then (1 : ℝ) else 0)
      ∂exponentialRace (w n))
    (∫ z, (if (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q
      then (1 : ℝ) else 0) ∂exponentialRace (w n))
    (∏ ell, Real.exp (-cycleTraceIntensity f ell.val) *
      cycleTraceIntensity f ell.val ^ q ell / ((q ell).factorial : ℝ))
  have ht' := abs_sub_le
    (∫ z, (if (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q
      then (1 : ℝ) else 0) ∂exponentialRace (w n))
    (∏ ell, Real.exp (-bulkCycleTraceIntensity f α ell.val) *
      bulkCycleTraceIntensity f α ell.val ^ q ell / ((q ell).factorial : ℝ))
    (∏ ell, Real.exp (-cycleTraceIntensity f ell.val) *
      cycleTraceIntensity f ell.val ^ q ell / ((q ell).factorial : ℝ))
  linarith

theorem cycle_point_indicator_integral {n : ℕ} (w : Weights n)
    (L : ℕ) (q : Fin L → ℕ) :
    (∫ z, (if cycleCountVector L (raceRankPermutation z) = q then (1 : ℝ) else 0)
      ∂exponentialRace w) =
      (exponentialRace w).real {z | cycleCountVector L (raceRankPermutation z) = q} := by
  classical
  have hF : Measurable (fun z : Fin n → ℝ => cycleCountVector L (raceRankPermutation z)) :=
    measurable_race_permutation_statistic (cycleCountVector L)
  have hm := measurableSet_eq_fun hF (measurable_const (a := q))
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
    integral_indicator_const (μ := exponentialRace w) (1 : ℝ) hm

theorem cycleVectorPoissonLaw_real_singleton {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (L : ℕ) (q : Fin L → ℕ) :
    (cycleVectorPoissonLaw f L).real {q} =
      ∏ ell, Real.exp (-cycleTraceIntensity f ell.val) *
        cycleTraceIntensity f ell.val ^ q ell / ((q ell).factorial : ℝ) := by
  unfold cycleVectorPoissonLaw
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro ell _
  rw [← measureReal_def, poissonMeasure_real_singleton,
    Real.coe_toNNReal _ (cycle_intensity_nonneg hf ell.val)]

theorem EndpointShellAssumption.cycle_point_probability_limit
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) :
    Tendsto (fun n => (exponentialRace (w n)).real
      {z | cycleCountVector L (raceRankPermutation z) = q}) atTop
      (𝓝 ((cycleVectorPoissonLaw f L).real {q})) := by
  rw [cycleVectorPoissonLaw_real_singleton hf L q]
  simpa only [cycle_point_indicator_integral] using
    hend.cycle_point_indicator_limit hnorm hf L q

end Luce
