import Luce.Section5IntensityBounds
import Luce.Section5ContractRepresentation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace Luce

def cycleInteriorCutoff (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ)+1)

theorem cycleInteriorCutoff_lt_one (n : ℕ) : cycleInteriorCutoff n < 1 := by
  unfold cycleInteriorCutoff
  have : 0 < (1 : ℝ) / ((n : ℝ)+1) := by positivity
  linarith

theorem cycleInteriorCutoff_tendsto : Tendsto cycleInteriorCutoff atTop (𝓝 1) := by
  unfold cycleInteriorCutoff
  simpa only [sub_zero] using
    tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem cyclic_cube_aecover (r : ℕ) :
    AECover (cyclicProfileMeasure r) atTop
      (fun n => cyclicBulkCube r (cycleInteriorCutoff n)) := by
  refine ⟨?_, fun _ => MeasurableSet.univ_pi (fun _ => measurableSet_Icc)⟩
  have hbase : ∀ᵐ x ∂profileMeasure, x ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [cyclic_ae_coordinates (r := r) hbase] with x hx
  have he : ∀ᶠ n in atTop, ∀ a, x a ≤ cycleInteriorCutoff n :=
    eventually_all.mpr (fun a => (cycleInteriorCutoff_tendsto.eventually
      (Ioi_mem_nhds (hx a).2)).mono (fun _ h => h.le))
  exact he.mono fun n hn a _ => ⟨(hx a).1.le, hn a⟩

theorem cyclicProfileMeasure_restrict_closed_bulk {r : ℕ} {α : ℝ} (hα : α < 1) :
    (cyclicProfileMeasure r).restrict (cyclicBulkCube r α) =
      volume.restrict (cyclicBulkCube r α) := by
  have hm : MeasurableSet (cyclicBulkCube r α) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [cyclicProfileMeasure_eq_closed_cube, Measure.restrict_restrict hm]
  congr 1
  apply Set.inter_eq_left.mpr
  intro x hx a ha
  exact ⟨(hx a ha).1, (hx a ha).2.trans hα.le⟩

theorem cycle_trace_nonneg_ae {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (k : ℕ) :
    ∀ᵐ x ∂cyclicProfileMeasure (k+1), 0 ≤ cycleTraceIntegrand f k x := by
  have hbase : ∀ᵐ x ∂profileMeasure, x ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [cyclic_ae_coordinates (r := k+1) hbase] with x hx
  apply Finset.prod_nonneg
  intro a _
  apply div_nonneg (rateKernel_nonneg (hf.2.1 (x a) (hx a)).le)
  exact (profileD_pos hf.integrable hf.ae_pos
    (profileQuantile_nonneg hf.integrable hf.ae_pos
      ⟨(hx (finRotate (k+1) a)).1.le, (hx (finRotate (k+1) a)).2⟩)).le

/-- Full cyclic-density integrability follows from first moments and the
raw shell condition. No finite-intensity assumption is used. -/
theorem EndpointShellAssumption.cycle_trace_integrable
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ) :
    Integrable (cycleTraceIntegrand f k) (cyclicProfileMeasure (k+1)) := by
  obtain ⟨C, hC⟩ := hend.bulk_intensity_bounded hnorm hf k
  apply (cyclic_cube_aecover (k+1)).integrable_of_integral_bounded_of_nonneg_ae
    (C * (k+1 : ℝ))
  · intro n
    unfold IntegrableOn
    rw [cyclicProfileMeasure_restrict_closed_bulk (cycleInteriorCutoff_lt_one n)]
    exact bulk_cycle_trace_integrable hf k (cycleInteriorCutoff_lt_one n)
  · exact cycle_trace_nonneg_ae hf k
  · apply Eventually.of_forall
    intro n
    rw [cyclicProfileMeasure_restrict_closed_bulk (cycleInteriorCutoff_lt_one n)]
    have h := hC (cycleInteriorCutoff n) (cycleInteriorCutoff_lt_one n)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mp h

theorem cycle_intensity_nonneg
    {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f) (k : ℕ) :
    0 ≤ cycleTraceIntensity f k := by
  exact mul_nonneg (by positivity) (integral_nonneg_of_ae (cycle_trace_nonneg_ae hf k))

theorem cyclic_cube_aecover_left (r : ℕ) :
    AECover (cyclicProfileMeasure r) (𝓝[<] (1 : ℝ)) (cyclicBulkCube r) := by
  refine ⟨?_, fun _ => MeasurableSet.univ_pi (fun _ => measurableSet_Icc)⟩
  have hbase : ∀ᵐ x ∂profileMeasure, x ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [cyclic_ae_coordinates (r := r) hbase] with x hx
  have he : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), ∀ a, x a ≤ α :=
    eventually_all.mpr (fun a => by
      have h : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), x a < α :=
        nhdsWithin_le_nhds (Ioi_mem_nhds (hx a).2)
      exact h.mono (fun _ ha => ha.le))
  exact he.mono fun α hα a _ => ⟨(hx a).1.le, hα a⟩

/-- Endpoint cutoff removal for the literal intensities, after proving
full integrability from the permitted inputs. -/
theorem EndpointShellAssumption.bulk_intensity_tendsto
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ) :
    Tendsto (fun α => bulkCycleTraceIntensity f α k) (𝓝[<] (1 : ℝ))
      (𝓝 (cycleTraceIntensity f k)) := by
  have h := ((cyclic_cube_aecover_left (k+1)).integral_tendsto_of_countably_generated
    (hend.cycle_trace_integrable hnorm hf k)).div_const (k+1 : ℝ)
  have he : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ),
      (∫ x in cyclicBulkCube (k+1) α, cycleTraceIntegrand f k x
        ∂cyclicProfileMeasure (k+1)) / (k+1 : ℝ) = bulkCycleTraceIntensity f α k := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    rw [cyclicProfileMeasure_restrict_closed_bulk hα]
    rfl
  have h' := h.congr' he
  simpa only [cycleTraceIntensity, div_eq_mul_inv, one_div, one_mul, mul_comm] using h'

end Luce
