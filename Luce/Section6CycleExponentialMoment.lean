import Luce.Section6PathVariation
import Luce.Section6LaplaceEnvelope

noncomputable section
open MeasureTheory
namespace Luce.Section6

theorem exp_pathVariation68_integrable {c : ℝ} (hc : 0 < c) (k : ℕ) (a b : ℝ) :
    Integrable (fun y : Fin k → ℝ => Real.exp (-c*pathVariation68 k a b y)) := by
  have he (x : ℝ) : Real.exp (-c*|x|) = (2/c)*laplaceDensity68 c x := by
    unfold laplaceDensity68
    field_simp
  have hi := ((laplaceDensity68_traceDensity hc).openPath_integral k a b).1.const_mul
    ((2/c)^(k+1))
  simp_rw [← openPathWeight68_exp, funext he, openPathWeight68_const_mul]
  exact hi

/-- Exponential control of the full relative-coordinate cycle measure.
The comparison is with a normalized Laplace density, so integrability
follows from the already proved path integral theorem. -/
theorem cycle_exponential_moment68 {p : ℝ → ℝ} (hp : TraceDensity68 p)
    {C g : ℝ} (hC : 0 ≤ C) (hg : 0 < g)
    (hb : ∀ x, p x ≤ C*Real.exp (-g*|x|)) (k : ℕ) :
    Integrable (fun y : Fin k → ℝ =>
      Real.exp ((g/4)*logTupleRange k (Fin.cons 0 y))*closedLogCycleWeight p k (Fin.cons 0 y)) := by
  have hW : Continuous (fun y : Fin k → ℝ => closedLogCycleWeight p k (Fin.cons 0 y)) := by
    simp_rw [closedLogCycleWeight_eq_openPath]
    have ht : Continuous (fun y : Fin k → ℝ => ((0 : ℝ), (0 : ℝ), y)) := by fun_prop
    exact (openPathWeight68_continuous hp.continuous k).comp ht
  have hR : Continuous (fun y : Fin k → ℝ => logTupleRange k (Fin.cons 0 y)) :=
    (logTupleRange_continuous68 k).comp (by fun_prop)
  apply ((exp_pathVariation68_integrable (half_pos hg) k 0 0).const_mul (C^(k+1))).mono'
    ((Real.continuous_exp.comp (continuous_const.mul hR)).mul hW).aestronglyMeasurable
  filter_upwards [] with y
  change ‖Real.exp ((g/4)*logTupleRange k (Fin.cons 0 y))*closedLogCycleWeight p k (Fin.cons 0 y)‖ ≤ _
  have hW0 : 0 ≤ closedLogCycleWeight p k (Fin.cons 0 y) := by
    rw [closedLogCycleWeight_eq_openPath]
    exact openPathWeight68_nonneg hp.nonneg _ _ _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hW0)]
  have hprod := openPathWeight68_mono hp.nonneg hb k 0 0 y
  rw [openPathWeight68_const_mul, openPathWeight68_exp] at hprod
  rw [closedLogCycleWeight_eq_openPath]
  calc
    _ ≤ Real.exp ((g/4)*logTupleRange k (Fin.cons 0 y))*
        (C^(k+1)*Real.exp (-g*pathVariation68 k 0 0 y)) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = C^(k+1)*Real.exp ((g/4)*logTupleRange k (Fin.cons 0 y)-g*pathVariation68 k 0 0 y) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ C^(k+1)*Real.exp (-(g/2)*pathVariation68 k 0 0 y) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC _)
      apply Real.exp_le_exp.mpr
      nlinarith [logTupleRange_le_pathVariation68 k 0 y]

theorem cycle_range_moment68 {p : ℝ → ℝ} (hp : TraceDensity68 p)
    {c : ℝ} (hc : 0 < c) (k : ℕ)
    (hi : Integrable (fun y : Fin k → ℝ => Real.exp (c*logTupleRange k (Fin.cons 0 y))*
      closedLogCycleWeight p k (Fin.cons 0 y))) :
    Integrable (fun y : Fin k → ℝ => logTupleRange k (Fin.cons 0 y)*
      closedLogCycleWeight p k (Fin.cons 0 y)) := by
  have hW : Continuous (fun y : Fin k → ℝ => closedLogCycleWeight p k (Fin.cons 0 y)) := by
    simp_rw [closedLogCycleWeight_eq_openPath]
    have ht : Continuous (fun y : Fin k → ℝ => ((0 : ℝ), (0 : ℝ), y)) := by fun_prop
    exact (openPathWeight68_continuous hp.continuous k).comp ht
  have hR : Continuous (fun y : Fin k → ℝ => logTupleRange k (Fin.cons 0 y)) :=
    (logTupleRange_continuous68 k).comp (by fun_prop)
  apply (hi.const_mul (1/c)).mono' (hR.mul hW).aestronglyMeasurable
  filter_upwards [] with y
  have hW0 : 0 ≤ closedLogCycleWeight p k (Fin.cons 0 y) := by
    rw [closedLogCycleWeight_eq_openPath]
    exact openPathWeight68_nonneg hp.nonneg _ _ _ _
  change ‖logTupleRange k (Fin.cons 0 y)*closedLogCycleWeight p k (Fin.cons 0 y)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (logTupleRange_nonneg _ _) hW0), ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ hW0
  have he := Real.add_one_le_exp (c*logTupleRange k (Fin.cons 0 y))
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ hc).mpr
  nlinarith

end Luce.Section6
