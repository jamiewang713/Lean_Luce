import Luce.Section6CycleExponentialMoment

noncomputable section
open MeasureTheory Set
namespace Luce.Section6

def relativeIdealTrace68 (p : ℝ → ℝ) (k : ℕ) (T : ℝ) : ℝ :=
  (∫ y : Fin k → ℝ, max (T-logTupleRange k (Fin.cons 0 y)) 0*
    closedLogCycleWeight p k (Fin.cons 0 y))/((k : ℝ)+1)

theorem closedLogCycleWeight_continuous68 {p : ℝ → ℝ} (hp : Continuous p) (k : ℕ) :
    Continuous (closedLogCycleWeight p k) := by
  unfold closedLogCycleWeight
  fun_prop

theorem closedLogCycleWeight_nonneg68 {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (k : ℕ) (x : Fin (k+1) → ℝ) : 0 ≤ closedLogCycleWeight p k x := by
  unfold closedLogCycleWeight
  exact Finset.prod_nonneg (fun j _ => hp _)

theorem relative_trace_integrable68 {p : ℝ → ℝ} (hp : TraceDensity68 p)
    (k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun y : Fin k → ℝ => max (T-logTupleRange k (Fin.cons 0 y)) 0*
      closedLogCycleWeight p k (Fin.cons 0 y)) := by
  have hcont : Continuous (fun y : Fin k → ℝ => max (T-logTupleRange k (Fin.cons 0 y)) 0*
      closedLogCycleWeight p k (Fin.cons 0 y)) := by
    have hR := (logTupleRange_continuous68 k).comp (show Continuous (Fin.cons (0 : ℝ)) by fun_prop)
    have hW := (closedLogCycleWeight_continuous68 hp.continuous k).comp
      (show Continuous (Fin.cons (0 : ℝ)) by fun_prop)
    exact ((continuous_const.sub hR).max continuous_const).mul hW
  apply ((hp.closedPath_integrable k 0).const_mul T).mono' hcont.aestronglyMeasurable
  filter_upwards [] with y
  change ‖max (T-logTupleRange k (Fin.cons 0 y)) 0*closedLogCycleWeight p k (Fin.cons 0 y)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _)
    (closedLogCycleWeight_nonneg68 hp.nonneg _ _))]
  exact mul_le_mul_of_nonneg_right (max_le (sub_le_self _ (logTupleRange_nonneg _ _)) hT)
    (closedLogCycleWeight_nonneg68 hp.nonneg _ _)

/-- The continuous total trace differs from its linear main term by a
uniformly bounded first range moment. -/
theorem relativeIdealTrace68_error {p : ℝ → ℝ} (hp : TraceDensity68 p) (k : ℕ)
    (hR : Integrable (fun y : Fin k → ℝ => logTupleRange k (Fin.cons 0 y)*
      closedLogCycleWeight p k (Fin.cons 0 y))) {T : ℝ} (hT : 0 ≤ T) :
    |relativeIdealTrace68 p k T-T*traceConvolution68 p k 0/((k : ℝ)+1)| ≤
      (∫ y : Fin k → ℝ, logTupleRange k (Fin.cons 0 y)*
        closedLogCycleWeight p k (Fin.cons 0 y))/((k : ℝ)+1) := by
  have hW := hp.closedPath_integrable k 0
  have htr := relative_trace_integrable68 hp k hT
  have hb : |(∫ y : Fin k → ℝ, max (T-logTupleRange k (Fin.cons 0 y)) 0*
      closedLogCycleWeight p k (Fin.cons 0 y))-T*traceConvolution68 p k 0| ≤
      ∫ y : Fin k → ℝ, logTupleRange k (Fin.cons 0 y)*closedLogCycleWeight p k (Fin.cons 0 y) := by
    rw [← hp.closedPath_integral k 0, ← integral_const_mul, ← integral_sub htr (hW.const_mul T)]
    rw [← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono (htr.sub (hW.const_mul T)).norm hR
    intro y
    have hw := closedLogCycleWeight_nonneg68 hp.nonneg k (Fin.cons 0 y)
    have hr := logTupleRange_nonneg k (Fin.cons 0 y)
    change |max (T-logTupleRange k (Fin.cons 0 y)) 0*closedLogCycleWeight p k (Fin.cons 0 y)-
      T*closedLogCycleWeight p k (Fin.cons 0 y)| ≤ _
    rw [abs_le]
    by_cases ht : logTupleRange k (Fin.cons 0 y) ≤ T
    · rw [max_eq_left (sub_nonneg.mpr ht)]
      constructor <;> nlinarith
    · rw [max_eq_right (by linarith : T-logTupleRange k (Fin.cons 0 y) ≤ 0)]
      constructor <;> nlinarith
  unfold relativeIdealTrace68
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < (k : ℝ)+1)]
  exact div_le_div_of_nonneg_right hb (by positivity)

/-- Length of the intersection of two intervals. -/
def clippedSpan68 (lo hi L U : ℝ) : ℝ := max (min hi U-max lo L) 0

theorem clippedSpan68_bounds {lo hi L U : ℝ} (h : lo ≤ hi) :
    0 ≤ clippedSpan68 lo hi L U ∧ clippedSpan68 lo hi L U ≤ hi-lo := by
  unfold clippedSpan68
  constructor
  · exact le_max_right _ _
  · apply max_le _ (sub_nonneg.mpr h)
    linarith [min_le_left hi U, le_max_left lo L]

theorem clippedSpan68_full {lo hi L U : ℝ} (h : lo ≤ hi) (hL : L ≤ lo) (hU : hi ≤ U) :
    clippedSpan68 lo hi L U = hi-lo := by
  simp only [clippedSpan68, min_eq_left hU, max_eq_left hL, max_eq_left (sub_nonneg.mpr h)]

def rootCoreSpan68 (side : Corner) (k : ℕ) (x : Fin (k+1) → ℝ) (L U lo hi : ℝ) : ℝ :=
  clippedSpan68 (lo-logTupleRoot side k x) (hi-logTupleRoot side k x)
    (L-logTupleRoot .right k x) (U-logTupleRoot .left k x)

theorem rootCoreSpan68_bounds (side : Corner) (k : ℕ) (x : Fin (k+1) → ℝ)
    (L U : ℝ) {lo hi : ℝ} (h : lo ≤ hi) :
    0 ≤ rootCoreSpan68 side k x L U lo hi ∧ rootCoreSpan68 side k x L U lo hi ≤ hi-lo := by
  simpa only [rootCoreSpan68, sub_sub_sub_cancel_right] using
    (clippedSpan68_bounds (L := L-logTupleRoot .right k x) (U := U-logTupleRoot .left k x)
      (sub_le_sub_right h (logTupleRoot side k x)))

theorem rootCoreSpan68_full (side : Corner) (k : ℕ) (x : Fin (k+1) → ℝ)
    {L U lo hi d : ℝ} (h : lo ≤ hi) (hL : L+d ≤ lo) (hU : hi+d ≤ U)
    (hR : logTupleRange k x ≤ d) : rootCoreSpan68 side k x L U lo hi = hi-lo := by
  have hminmax : logTupleRoot .right k x ≤ logTupleRoot .left k x :=
    sub_nonneg.mp (logTupleRange_nonneg k x)
  have hrlo : logTupleRoot .right k x ≤ logTupleRoot side k x := by cases side <;> simp_all
  have hrhi : logTupleRoot side k x ≤ logTupleRoot .left k x := by cases side <;> simp_all
  unfold rootCoreSpan68
  rw [clippedSpan68_full (sub_le_sub_right h _) (by unfold logTupleRange at hR; linarith)
    (by unfold logTupleRange at hR; linarith)]
  ring

end Luce.Section6
