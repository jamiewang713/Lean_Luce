import Luce.Section6ContinuousTraceBounds

noncomputable section
open MeasureTheory
namespace Luce.Section6

def cycleRangeMass68 (p : ℝ → ℝ) (k : ℕ) : ℝ :=
  (∫ y : Fin k → ℝ, logTupleRange k (Fin.cons 0 y)*
    closedLogCycleWeight p k (Fin.cons 0 y))/((k : ℝ)+1)

/-- The constant boundary correction is independent of the interval.
Its remaining error is exponentially small in the logarithmic width. -/
theorem relativeIdealTrace68_remainder {p : ℝ → ℝ} (hp : TraceDensity68 p)
    {c : ℝ} (hc : 0 < c) (k : ℕ)
    (hE : Integrable (fun y : Fin k → ℝ => Real.exp (c*logTupleRange k (Fin.cons 0 y))*
      closedLogCycleWeight p k (Fin.cons 0 y))) {T : ℝ} (hT : 0 ≤ T) :
    |relativeIdealTrace68 p k T-T*traceConvolution68 p k 0/((k : ℝ)+1)+cycleRangeMass68 p k| ≤
      ((∫ y : Fin k → ℝ, Real.exp (c*logTupleRange k (Fin.cons 0 y))*
        closedLogCycleWeight p k (Fin.cons 0 y))/(c*((k : ℝ)+1)))*Real.exp (-c*T) := by
  have hR := cycle_range_moment68 hp hc k hE
  have hW := hp.closedPath_integrable k 0
  have htr := relative_trace_integrable68 hp k hT
  have hcont : Continuous (fun y : Fin k → ℝ => max (logTupleRange k (Fin.cons 0 y)-T) 0*
      closedLogCycleWeight p k (Fin.cons 0 y)) := by
    have hR := (logTupleRange_continuous68 k).comp (show Continuous (Fin.cons (0 : ℝ)) by fun_prop)
    have hW := (closedLogCycleWeight_continuous68 hp.continuous k).comp
      (show Continuous (Fin.cons (0 : ℝ)) by fun_prop)
    exact ((hR.sub continuous_const).max continuous_const).mul hW
  have hrem : Integrable (fun y : Fin k → ℝ => max (logTupleRange k (Fin.cons 0 y)-T) 0*
      closedLogCycleWeight p k (Fin.cons 0 y)) := by
    apply hR.mono' hcont.aestronglyMeasurable
    filter_upwards [] with y
    have hw := closedLogCycleWeight_nonneg68 hp.nonneg k (Fin.cons 0 y)
    change ‖max (logTupleRange k (Fin.cons 0 y)-T) 0*closedLogCycleWeight p k (Fin.cons 0 y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) hw)]
    exact mul_le_mul_of_nonneg_right (max_le (sub_le_self _ hT) (logTupleRange_nonneg _ _)) hw
  have hid (y : Fin k → ℝ) :
      max (T-logTupleRange k (Fin.cons 0 y)) 0*closedLogCycleWeight p k (Fin.cons 0 y)-
        T*closedLogCycleWeight p k (Fin.cons 0 y)+
        logTupleRange k (Fin.cons 0 y)*closedLogCycleWeight p k (Fin.cons 0 y) =
      max (logTupleRange k (Fin.cons 0 y)-T) 0*closedLogCycleWeight p k (Fin.cons 0 y) := by
    by_cases h : logTupleRange k (Fin.cons 0 y) ≤ T
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]; ring
    · rw [max_eq_right (by linarith : T-logTupleRange k (Fin.cons 0 y) ≤ 0),
        max_eq_left (by linarith : 0 ≤ logTupleRange k (Fin.cons 0 y)-T)]; ring
  have hidI : (∫ y : Fin k → ℝ, max (T-logTupleRange k (Fin.cons 0 y)) 0*
      closedLogCycleWeight p k (Fin.cons 0 y))-T*traceConvolution68 p k 0+
      (∫ y : Fin k → ℝ, logTupleRange k (Fin.cons 0 y)*closedLogCycleWeight p k (Fin.cons 0 y)) =
      ∫ y : Fin k → ℝ, max (logTupleRange k (Fin.cons 0 y)-T) 0*closedLogCycleWeight p k (Fin.cons 0 y) := by
    rw [← hp.closedPath_integral k 0, ← integral_const_mul, ← integral_sub htr (hW.const_mul T)]
    have hs : Integrable (fun y : Fin k → ℝ => max (T-logTupleRange k (Fin.cons 0 y)) 0*
        closedLogCycleWeight p k (Fin.cons 0 y)-T*closedLogCycleWeight p k (Fin.cons 0 y)) :=
      htr.sub (hW.const_mul T)
    rw [← integral_add hs hR]
    exact integral_congr_ae (Filter.Eventually.of_forall hid)
  have hpoint (r : ℝ) : max (r-T) 0 ≤ (Real.exp (-c*T)/c)*Real.exp (c*r) := by
    by_cases h : r ≤ T
    · rw [max_eq_right (sub_nonpos.mpr h)]; positivity
    · rw [max_eq_left (by linarith : 0 ≤ r-T)]
      have he := Real.add_one_le_exp (c*(r-T))
      have hx : (Real.exp (-c*T)/c)*Real.exp (c*r) = Real.exp (c*(r-T))/c := by
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        congr 2
        ring
      rw [hx]
      apply (le_div_iff₀ hc).mpr
      nlinarith
  have hb := integral_mono hrem (hE.const_mul (Real.exp (-c*T)/c)) (fun y => by
    have hw := closedLogCycleWeight_nonneg68 hp.nonneg k (Fin.cons 0 y)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hpoint (logTupleRange k (Fin.cons 0 y))) hw)
  rw [integral_const_mul] at hb
  unfold relativeIdealTrace68 cycleRangeMass68
  rw [← sub_div, ← add_div, hidI, abs_div,
    abs_of_pos (by positivity : 0 < (k : ℝ)+1),
    abs_of_nonneg (integral_nonneg (fun y => mul_nonneg (le_max_right _ _)
      (closedLogCycleWeight_nonneg68 hp.nonneg _ _)))]
  apply (div_le_div_of_nonneg_right hb (by positivity)).trans_eq
  field_simp

end Luce.Section6
