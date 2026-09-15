import Luce.ExponentialRace
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # Atomless exponential clocks and almost-surely distinct ranks -/

open MeasureTheory ProbabilityTheory Set

namespace Luce

instance expMeasure_nullSingleton (r : ℝ) : NullSingletonClass (expMeasure r) := by
  change NullSingletonClass (volume.withDensity (exponentialPDF r))
  infer_instance

lemma expMeasure_Ici {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    expMeasure r (Ici t) = ENNReal.ofReal (Real.exp (-(r * t))) := by
  rw [← measure_congr (Ioi_ae_eq_Ici (μ := expMeasure r))]
  exact expMeasure_Ioi hr ht

lemma exponentialRace_survival_ge {n : ℕ} (w : Weights n) (i : Fin n)
    (t : ℝ) (ht : 0 ≤ t) :
    exponentialRace w {clocks | t ≤ clocks i} =
      ENNReal.ofReal (Real.exp (-(w.rate i * t))) := by
  calc
    _ = expMeasure (w.rate i) (Ici t) :=
      (exponentialRace_eval w i).measure_preimage measurableSet_Ici.nullMeasurableSet
    _ = _ := expMeasure_Ici (w.positive i) ht

lemma exponentialRace_collision_zero {n : ℕ} (w : Weights n) {i j : Fin n} (hij : i ≠ j) :
    exponentialRace w {clocks | clocks i = clocks j} = 0 := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  letI := isProbabilityMeasure_expMeasure (w.positive j)
  have h := (exponentialRace_independent w).indepFun hij
  have hm := h.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable
  rw [(exponentialRace_eval w i).map_eq, (exponentialRace_eval w j).map_eq] at hm
  have he : {clocks : Fin n → ℝ | clocks i = clocks j} =
      (fun clocks => (clocks i, clocks j)) ⁻¹' Set.diagonal ℝ := rfl
  rw [he, ← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    measurableSet_diagonal, hm, Measure.prod_apply measurableSet_diagonal]
  simp [Set.diagonal, eq_comm]

/-- Independent exponential clocks are pairwise distinct almost surely. -/
theorem exponentialRace_injective_ae {n : ℕ} (w : Weights n) :
    ∀ᵐ clocks ∂exponentialRace w, Function.Injective clocks := by
  have hpair : ∀ i j : Fin n, ∀ᵐ clocks ∂exponentialRace w,
      clocks i = clocks j → i = j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ _ => hij
    · have hn : ∀ᵐ clocks ∂exponentialRace w, clocks i ≠ clocks j := by
        rw [ae_iff]
        simpa only [not_not] using exponentialRace_collision_zero w hij
      exact hn.mono fun _ hne he => (hne he).elim
  exact (ae_all_iff.mpr fun i => ae_all_iff.mpr (hpair i))

end Luce

