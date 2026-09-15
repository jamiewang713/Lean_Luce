import Luce.Section6ContinuousTraceRemainder

noncomputable section
open MeasureTheory Set
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

def logTraceBox68 (k : ℕ) (L U : ℝ) : Set (Fin (k+1) → ℝ) :=
  Set.pi Set.univ (fun _ => Ioc L U)

theorem logTraceBox68_measurable (k : ℕ) (L U : ℝ) : MeasurableSet (logTraceBox68 k L U) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem logTraceBox68_integrable {p : ℝ → ℝ} (hp : Continuous p) (k : ℕ) (L U : ℝ) :
    IntegrableOn (closedLogCycleWeight p k) (logTraceBox68 k L U) := by
  apply (closedLogCycleWeight_continuous68 hp k).integrableOn_Icc.mono_set
    (t := Icc (fun _ => L) (fun _ => U))
  intro x hx
  constructor <;> intro j
  · exact ((hx j (mem_univ j)).1).le
  · exact (hx j (mem_univ j)).2

theorem translated_box_Ioc_iff68 (k : ℕ) (x : Fin (k+1) → ℝ) (L U s : ℝ) :
    (∀ j, L < s+x j ∧ s+x j ≤ U) ↔
      s ∈ Ioc (L-logTupleRoot .right k x) (U-logTupleRoot .left k x) := by
  constructor
  · intro h
    have hl : L-s < logTupleRoot .right k x :=
      (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => by linarith [(h j).1])
    have hu : logTupleRoot .left k x ≤ U-s :=
      Finset.sup'_le Finset.univ_nonempty x (fun j _ => by linarith [(h j).2])
    constructor <;> linarith
  · intro h j
    have hl : logTupleRoot .right k x ≤ x j := Finset.inf'_le x (Finset.mem_univ j)
    have hu : x j ≤ logTupleRoot .left k x := Finset.le_sup' x (Finset.mem_univ j)
    constructor <;> linarith [h.1,h.2]

theorem continuous_trace_first_coordinate_Ioc68 (p : ℝ → ℝ) (k : ℕ)
    (x : Fin (k+1) → ℝ) (L U : ℝ) :
    (∫ s : ℝ, if (∀ j, L < s+x j ∧ s+x j ≤ U)
      then closedLogCycleWeight p k x else 0) =
      max (U-L-logTupleRange k x) 0*closedLogCycleWeight p k x := by
  simp_rw [translated_box_Ioc_iff68]
  have he := integral_indicator_const (μ := (volume : Measure ℝ)) (closedLogCycleWeight p k x)
    (measurableSet_Ioc (a := L-logTupleRoot .right k x) (b := U-logTupleRoot .left k x))
  simp only [Set.indicator_apply, smul_eq_mul, Real.volume_real_Ioc] at he
  rw [he]
  congr 2
  unfold logTupleRange
  ring

theorem translated_trace_integrable68 {p : ℝ → ℝ} (hp : TraceDensity68 p)
    (k : ℕ) {L U : ℝ} (hLU : L ≤ U) :
    Integrable (fun z : (Fin k → ℝ) × ℝ =>
      if (∀ j, L < z.2+(Fin.cons 0 z.1 : Fin (k+1) → ℝ) j ∧
        z.2+(Fin.cons 0 z.1 : Fin (k+1) → ℝ) j ≤ U)
      then closedLogCycleWeight p k (Fin.cons 0 z.1) else 0)
      ((volume : Measure (Fin k → ℝ)).prod volume) := by
  have hc : Continuous (fun z : (Fin k → ℝ) × ℝ => closedLogCycleWeight p k (Fin.cons 0 z.1)) :=
    (closedLogCycleWeight_continuous68 hp.continuous k).comp (by fun_prop)
  have hm : MeasurableSet {z : (Fin k → ℝ) × ℝ | ∀ j,
      L < z.2+(Fin.cons 0 z.1 : Fin (k+1) → ℝ) j ∧
      z.2+(Fin.cons 0 z.1 : Fin (k+1) → ℝ) j ≤ U} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    have hcoord : Continuous (fun z : (Fin k → ℝ) × ℝ => z.2+(Fin.cons 0 z.1 : Fin (k+1) → ℝ) j) := by fun_prop
    exact ((isOpen_lt continuous_const hcoord).measurableSet).inter
      ((isClosed_le hcoord continuous_const).measurableSet)
  have hmeas : AEStronglyMeasurable (fun z : (Fin k → ℝ) × ℝ =>
      if (∀ j, L < z.2+(Fin.cons 0 z.1 : Fin (k+1) → ℝ) j ∧
        z.2+(Fin.cons 0 z.1 : Fin (k+1) → ℝ) j ≤ U)
      then closedLogCycleWeight p k (Fin.cons 0 z.1) else 0)
      ((volume : Measure (Fin k → ℝ)).prod volume) := by
    convert (hc.aestronglyMeasurable (μ := ((volume : Measure (Fin k → ℝ)).prod volume))).indicator hm using 1 <;>
      first | rfl | (funext z; simp only [Set.indicator_apply] <;> rfl)
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro y
    simp only [translated_box_Ioc_iff68]
    have hi : IntegrableOn (fun _ : ℝ => closedLogCycleWeight p k (Fin.cons 0 y))
        (Ioc (L-logTupleRoot .right k (Fin.cons 0 y)) (U-logTupleRoot .left k (Fin.cons 0 y))) :=
      integrable_const _
    convert hi.integrable_indicator measurableSet_Ioc using 1 <;>
      first | rfl | (funext s; simp only [Set.indicator_apply] <;> rfl)
  · have he (y : Fin k → ℝ) :
        (∫ s : ℝ, ‖if (∀ j, L < s+(Fin.cons 0 y : Fin (k+1) → ℝ) j ∧
          s+(Fin.cons 0 y : Fin (k+1) → ℝ) j ≤ U)
          then closedLogCycleWeight p k (Fin.cons 0 y) else 0‖) =
        max (U-L-logTupleRange k (Fin.cons 0 y)) 0*closedLogCycleWeight p k (Fin.cons 0 y) := by
      have hn (s : ℝ) : 0 ≤ (if (∀ j, L < s+(Fin.cons 0 y : Fin (k+1) → ℝ) j ∧
          s+(Fin.cons 0 y : Fin (k+1) → ℝ) j ≤ U)
          then closedLogCycleWeight p k (Fin.cons 0 y) else 0) := by
        split_ifs <;> first | exact closedLogCycleWeight_nonneg68 hp.nonneg _ _ | rfl
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (hn _)]
      exact continuous_trace_first_coordinate_Ioc68 p k (Fin.cons 0 y) L U
    simpa only [he] using relative_trace_integrable68 hp k (sub_nonneg.mpr hLU)

theorem continuous_box_trace_integral68 {p : ℝ → ℝ} (hp : TraceDensity68 p)
    (k : ℕ) {L U : ℝ} (hLU : L ≤ U) :
    (∫ x in logTraceBox68 k L U, closedLogCycleWeight p k x) =
      ∫ y : Fin k → ℝ, max (U-L-logTupleRange k (Fin.cons 0 y)) 0*
        closedLogCycleWeight p k (Fin.cons 0 y) := by
  have hi := (logTraceBox68_integrable hp.continuous k L U).integrable_indicator
    (logTraceBox68_measurable k L U)
  have ht := translated_trace_integrable68 hp k hLU
  have hcons (s : ℝ) (y : Fin k → ℝ) :
      (Fin.cons s ((fun _ : Fin k => s)+y) : Fin (k+1) → ℝ) = fun j => s+(Fin.cons 0 y : Fin (k+1) → ℝ) j := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  calc
    _ = ∫ s : ℝ, ∫ z : Fin k → ℝ,
        (logTraceBox68 k L U).indicator (closedLogCycleWeight p k) (Fin.cons s z) := by
      rw [← integral_indicator (logTraceBox68_measurable k L U)]
      exact integral_fin_cons68 _ hi
    _ = ∫ s : ℝ, ∫ y : Fin k → ℝ,
        if (∀ j, L < s+(Fin.cons 0 y : Fin (k+1) → ℝ) j ∧
          s+(Fin.cons 0 y : Fin (k+1) → ℝ) j ≤ U)
        then closedLogCycleWeight p k (Fin.cons 0 y) else 0 := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [← integral_add_left_eq_self
        (fun z : Fin k → ℝ => (logTraceBox68 k L U).indicator (closedLogCycleWeight p k) (Fin.cons s z))
        (fun _ : Fin k => s)]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [Pi.add_apply, hcons, Set.indicator_apply, logTraceBox68, Set.mem_pi,
        Set.mem_univ, forall_const, Set.mem_Ioc, closedLogCycleWeight_translate]
    _ = ∫ y : Fin k → ℝ, ∫ s : ℝ,
        if (∀ j, L < s+(Fin.cons 0 y : Fin (k+1) → ℝ) j ∧
          s+(Fin.cons 0 y : Fin (k+1) → ℝ) j ≤ U)
        then closedLogCycleWeight p k (Fin.cons 0 y) else 0 := integral_integral_swap ht.swap
    _ = _ := by simp_rw [continuous_trace_first_coordinate_Ioc68]

theorem continuous_box_trace_bound68 {p : ℝ → ℝ} (hp : TraceDensity68 p)
    (k : ℕ) {L U : ℝ} (hLU : L ≤ U) :
    (∫ x in logTraceBox68 k L U, closedLogCycleWeight p k x) ≤ (U-L)*traceConvolution68 p k 0 := by
  rw [continuous_box_trace_integral68 hp k hLU, ← hp.closedPath_integral k 0, ← integral_const_mul]
  apply integral_mono (relative_trace_integrable68 hp k (sub_nonneg.mpr hLU))
    ((hp.closedPath_integrable k 0).const_mul (U-L))
  intro y
  exact mul_le_mul_of_nonneg_right (max_le (sub_le_self _ (logTupleRange_nonneg _ _)) (sub_nonneg.mpr hLU))
    (closedLogCycleWeight_nonneg68 hp.nonneg _ _)

end Luce.Section6
