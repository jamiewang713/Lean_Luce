import Luce.Section6PathIntegral
import Luce.Section6ContinuousTraceGeometry

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem openPathWeight68_eq_prod (p : ℝ → ℝ) (k : ℕ) (a b : ℝ)
    (y : Fin k → ℝ) :
    openPathWeight68 p k a b y =
      ∏ j : Fin (k+1), p ((Fin.cons a y : Fin (k+1) → ℝ) j-
        (Fin.snoc y b : Fin (k+1) → ℝ) j) := by
  induction k generalizing a b with
  | zero => simp [openPathWeight68, Fin.snoc_zero]
  | succ k ih =>
    obtain ⟨s, z, rfl⟩ := Fin.exists_cons y
    simp only [openPathWeight68, Fin.cons_zero, Fin.tail_cons,
      ← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ, Fin.cons_succ, ih]

theorem closedLogCycleWeight_eq_openPath (p : ℝ → ℝ) (k : ℕ) (a : ℝ)
    (y : Fin k → ℝ) :
    closedLogCycleWeight p k (Fin.cons a y) = openPathWeight68 p k a a y := by
  rw [openPathWeight68_eq_prod]
  unfold closedLogCycleWeight
  simp only [Fin.snoc_eq_cons_rotate]

theorem TraceDensity68.closedPath_integrable {p : ℝ → ℝ} (hp : TraceDensity68 p)
    (k : ℕ) (a : ℝ) : Integrable (fun y : Fin k → ℝ => closedLogCycleWeight p k (Fin.cons a y)) := by
  simp_rw [closedLogCycleWeight_eq_openPath]
  exact (hp.openPath_integral k a a).1

/-- The full relative-coordinate integral gives the return density;
there is no orthant, choice of a unique extremum, or tie exceptional set. -/
theorem TraceDensity68.closedPath_integral {p : ℝ → ℝ} (hp : TraceDensity68 p)
    (k : ℕ) (a : ℝ) :
    (∫ y : Fin k → ℝ, closedLogCycleWeight p k (Fin.cons a y)) = traceConvolution68 p k 0 := by
  simp_rw [closedLogCycleWeight_eq_openPath]
  simpa only [sub_self] using (hp.openPath_integral k a a).2

/-- Exact continuous root-localized trace before the core is imposed. -/
theorem TraceDensity68.continuous_root_trace {p : ℝ → ℝ} (hp : TraceDensity68 p)
    (side : Corner) (k : ℕ) {lo hi : ℝ} (hlohi : lo ≤ hi) :
    (∫ y : Fin k → ℝ, ∫ r : ℝ,
      if lo < logTupleRoot side k (fun j => r+(Fin.cons 0 y : Fin (k+1) → ℝ) j) ∧
        logTupleRoot side k (fun j => r+(Fin.cons 0 y : Fin (k+1) → ℝ) j) ≤ hi
      then closedLogCycleWeight p k (fun j => r+(Fin.cons 0 y : Fin (k+1) → ℝ) j) else 0) / ((k : ℝ)+1) =
      (hi-lo)*traceConvolution68 p k 0/((k : ℝ)+1) := by
  simp_rw [continuous_root_first_coordinate p side k _ hlohi]
  rw [integral_const_mul, hp.closedPath_integral k 0]

end Luce.Section6
