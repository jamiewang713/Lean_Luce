import Luce.Section6IdealTraceDefinitions
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

def closedLogCycleWeight (p : ℝ → ℝ) (k : ℕ) (x : Fin (k+1) → ℝ) : ℝ :=
  ∏ j, p (x j-x (finRotate (k+1) j))

def logTupleRoot (side : Corner) (k : ℕ) (x : Fin (k+1) → ℝ) : ℝ :=
  match side with
  | .right => Finset.univ.inf' Finset.univ_nonempty x
  | .left => Finset.univ.sup' Finset.univ_nonempty x

def logTupleRange (k : ℕ) (x : Fin (k+1) → ℝ) : ℝ :=
  logTupleRoot .left k x - logTupleRoot .right k x

theorem closedLogCycleWeight_translate (p : ℝ → ℝ) (k : ℕ)
    (x : Fin (k+1) → ℝ) (r : ℝ) :
    closedLogCycleWeight p k (fun j => r+x j) = closedLogCycleWeight p k x := by
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  ring

theorem logTupleRoot_translate (side : Corner) (k : ℕ)
    (x : Fin (k+1) → ℝ) (r : ℝ) :
    logTupleRoot side k (fun j => r+x j) = r+logTupleRoot side k x := by
  cases side
  · exact (map_finset_sup' (OrderIso.addLeft r) Finset.univ_nonempty x).symm
  · exact (map_finset_inf' (OrderIso.addLeft r) Finset.univ_nonempty x).symm

theorem logTupleRange_nonneg (k : ℕ) (x : Fin (k+1) → ℝ) :
    0 ≤ logTupleRange k x := by
  apply sub_nonneg.mpr
  exact (Finset.inf'_le x (Finset.mem_univ (0 : Fin (k+1)))).trans
    (Finset.le_sup' x (Finset.mem_univ (0 : Fin (k+1))))

theorem translated_box_iff (k : ℕ) (x : Fin (k+1) → ℝ) (lo hi r : ℝ) :
    (∀ j, lo ≤ r+x j ∧ r+x j ≤ hi) ↔
      lo-logTupleRoot .right k x ≤ r ∧ r ≤ hi-logTupleRoot .left k x := by
  constructor
  · intro h
    have hl : lo-r ≤ logTupleRoot .right k x :=
      Finset.le_inf' Finset.univ_nonempty x (fun j _ => by linarith [(h j).1])
    have hu : logTupleRoot .left k x ≤ hi-r :=
      Finset.sup'_le Finset.univ_nonempty x (fun j _ => by linarith [(h j).2])
    constructor <;> linarith
  · intro h j
    have hl : logTupleRoot .right k x ≤ x j := Finset.inf'_le x (Finset.mem_univ j)
    have hu : x j ≤ logTupleRoot .left k x := Finset.le_sup' x (Finset.mem_univ j)
    constructor <;> linarith [h.1, h.2]

/-- The first-coordinate integral of a translation-invariant cycle product
over a box has exactly the manuscript's (T-range)_+ factor. -/
theorem continuous_trace_first_coordinate (p : ℝ → ℝ) (k : ℕ)
    (x : Fin (k+1) → ℝ) (lo hi : ℝ) :
    (∫ r : ℝ, if (∀ j, lo ≤ r+x j ∧ r+x j ≤ hi)
      then closedLogCycleWeight p k (fun j => r+x j) else 0) =
      max (hi-lo-logTupleRange k x) 0 * closedLogCycleWeight p k x := by
  simp_rw [closedLogCycleWeight_translate, translated_box_iff]
  have he := integral_indicator_const (μ := (volume : Measure ℝ))
    (closedLogCycleWeight p k x)
    (measurableSet_Icc (a := lo-logTupleRoot .right k x) (b := hi-logTupleRoot .left k x))
  simp only [Set.indicator_apply, Set.mem_Icc, smul_eq_mul, Real.volume_real_Icc] at he
  rw [he]
  congr 2
  unfold logTupleRange
  ring

/-- Root localization can be integrated without an extremum-rotation
argument: for fixed relative positions, either canonical root is translated
by r, and the allowed interval for r has length hi-lo. -/
theorem continuous_root_first_coordinate (p : ℝ → ℝ) (side : Corner) (k : ℕ)
    (x : Fin (k+1) → ℝ) {lo hi : ℝ} (hlohi : lo ≤ hi) :
    (∫ r : ℝ, if lo < logTupleRoot side k (fun j => r+x j) ∧
      logTupleRoot side k (fun j => r+x j) ≤ hi
      then closedLogCycleWeight p k (fun j => r+x j) else 0) =
      (hi-lo)*closedLogCycleWeight p k x := by
  simp_rw [closedLogCycleWeight_translate, logTupleRoot_translate]
  have hevent (r : ℝ) :
      (lo < r+logTupleRoot side k x ∧ r+logTupleRoot side k x ≤ hi) ↔
      r ∈ Ioc (lo-logTupleRoot side k x) (hi-logTupleRoot side k x) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp_rw [hevent]
  have he := integral_indicator_const (μ := (volume : Measure ℝ))
    (closedLogCycleWeight p k x)
    (measurableSet_Ioc (a := lo-logTupleRoot side k x) (b := hi-logTupleRoot side k x))
  simp only [Set.indicator_apply, smul_eq_mul,
    Real.volume_real_Ioc_of_le (sub_le_sub_right hlohi _)] at he
  rw [he]
  congr 1
  ring

end Luce.Section6
