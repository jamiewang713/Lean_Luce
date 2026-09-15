import Luce.Section6LogCellQuadrature

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce.Section6

theorem sum_logCellCube68_integrals {A B k : ℕ} {f : (Fin (k+1) → ℝ) → ℝ} (hf : Continuous f) :
    (∑ a : IdealDepthTuple A B k, ∫ x in logCellCube68 a, f x) =
      ∫ x in logTraceBox68 k (Real.log (A : ℝ)) (Real.log ((B+1 : ℕ) : ℝ)), f x := by
  have h := integral_iUnion_fintype (logCellCube68_measurable (A := A) (B := B) (k := k))
    (logCellCube68_disjoint A B k) (fun a => logCellCube68_integrable a hf)
  rw [logCellCube68_union] at h
  exact h.symm

def logGridTrace68 (p : ℝ → ℝ) (k A B : ℕ) : ℝ :=
  (∑ a : IdealDepthTuple A B k, closedLogCycleWeight p k (fun j => Real.log ((a j).val : ℝ))*
    (∏ j, 1/((a j).val : ℝ)))/((k : ℝ)+1)

theorem log_grid_raw_comparison68 {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hd : Differentiable ℝ p) {C g : ℝ} (hC : 0 ≤ C) (hg : 0 ≤ g)
    (hb : ∀ x, p x+‖deriv p x‖ ≤ C*Real.exp (-g*|x|))
    (k : ℕ) {A B : ℕ} (hA : 1 ≤ A) :
    |(∑ a : IdealDepthTuple A B k, closedLogCycleWeight p k (fun j => Real.log ((a j).val : ℝ))*
      (∏ j, 1/((a j).val : ℝ)))-
      ∫ x in logTraceBox68 k (Real.log (A : ℝ)) (Real.log ((B+1 : ℕ) : ℝ)), closedLogCycleWeight p k x| ≤
    (logGridErrorConstant68 C g k/(A : ℝ))*
      ∫ x in logTraceBox68 k (Real.log (A : ℝ)) (Real.log ((B+1 : ℕ) : ℝ)),
        closedLogCycleWeight (fun t => Real.exp (-g*|t|)) k x := by
  rw [← sum_logCellCube68_integrals (closedLogCycleWeight_continuous68 hd.continuous k),
    ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a : IdealDepthTuple A B k, (logGridErrorConstant68 C g k/(A : ℝ))*
        ∫ x in logCellCube68 a, closedLogCycleWeight (fun t => Real.exp (-g*|t|)) k x :=
      Finset.sum_le_sum (fun a _ => logCellCube68_integral_error hp hd hC hg hb hA a)
    _ = _ := by
      rw [← Finset.mul_sum, sum_logCellCube68_integrals (closedLogCycleWeight_continuous68 (by fun_prop) k)]

def logEnvelopeTraceBound68 (g : ℝ) (k : ℕ) : ℝ := (2/g)^(k+1)*(g/2)

theorem log_envelope_box_bound68 {g : ℝ} (hg : 0 < g) (k : ℕ) {L U : ℝ} (hLU : L ≤ U) :
    (∫ x in logTraceBox68 k L U, closedLogCycleWeight (fun t => Real.exp (-g*|t|)) k x) ≤
      logEnvelopeTraceBound68 g k*(U-L) := by
  have he (t : ℝ) : Real.exp (-g*|t|) = (2/g)*laplaceDensity68 g t := by
    unfold laplaceDensity68
    field_simp
  have hp := laplaceDensity68_traceDensity hg
  have hmax : ∀ t, laplaceDensity68 g t ≤ g/2 := by
    intro t
    unfold laplaceDensity68
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (abs_nonneg _)))
  simp_rw [funext he, closedLogCycleWeight_const_mul68]
  rw [integral_const_mul]
  have hh := (continuous_box_trace_bound68 hp k hLU).trans
    (mul_le_mul_of_nonneg_left (hp.convolution_bound hmax k 0) (sub_nonneg.mpr hLU))
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by unfold logEnvelopeTraceBound68; ring)

/-- Quantitative cubature, uniformly in the upper cutoff, with all ordered
tuples still present. The error grows only linearly with log(B/A). -/
theorem logGridTrace68_comparison {p : ℝ → ℝ} (hp : TraceDensity68 p)
    (hd : Differentiable ℝ p) {C g : ℝ} (hC : 0 ≤ C) (hg : 0 < g)
    (hb : ∀ x, p x+‖deriv p x‖ ≤ C*Real.exp (-g*|x|))
    (k : ℕ) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    |logGridTrace68 p k A B-relativeIdealTrace68 p k
      (Real.log ((B+1 : ℕ) : ℝ)-Real.log (A : ℝ))| ≤
    (logGridErrorConstant68 C g k*logEnvelopeTraceBound68 g k/((k : ℝ)+1))*
      ((Real.log ((B+1 : ℕ) : ℝ)-Real.log (A : ℝ))/(A : ℝ)) := by
  have hLU := monotone_nat_log68 (hAB.trans (Nat.le_succ B))
  have hh := log_grid_raw_comparison68 hp.nonneg hd hC hg.le hb k hA (B := B)
  have hK : 0 ≤ logGridErrorConstant68 C g k/(A : ℝ) := by unfold logGridErrorConstant68; positivity
  have he := hh.trans (mul_le_mul_of_nonneg_left (log_envelope_box_bound68 hg k hLU) hK)
  rw [continuous_box_trace_integral68 hp k hLU] at he
  unfold logGridTrace68 relativeIdealTrace68
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < (k : ℝ)+1)]
  exact (div_le_div_of_nonneg_right he (by positivity)).trans_eq (by ring)

end Luce.Section6
