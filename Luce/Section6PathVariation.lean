import Luce.Section6ClosedPathIntegral

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

def pathVariation68 : (k : ℕ) → ℝ → ℝ → (Fin k → ℝ) → ℝ
  | 0, a, b, _ => |a-b|
  | k+1, a, b, y => |a-y 0|+pathVariation68 k (y 0) b (Fin.tail y)

theorem pathVariation68_nonneg (k : ℕ) (a b : ℝ) (y : Fin k → ℝ) :
    0 ≤ pathVariation68 k a b y := by
  induction k generalizing a b with
  | zero => exact abs_nonneg _
  | succ k ih => exact add_nonneg (abs_nonneg _) (ih _ _ _)

theorem pathVariation68_vertex (k : ℕ) (a b : ℝ) (y : Fin k → ℝ) (j : Fin k) :
    |a-y j| ≤ pathVariation68 k a b y := by
  induction k generalizing a b with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · exact le_add_of_nonneg_right (pathVariation68_nonneg k _ _ _)
    · have hv := ih (y 0) b (Fin.tail y) i
      have ht := abs_sub_le a (y 0) (y i.succ)
      change |y 0-y i.succ| ≤ pathVariation68 k (y 0) b (Fin.tail y) at hv
      change |a-y i.succ| ≤ |a-y 0|+pathVariation68 k (y 0) b (Fin.tail y)
      linarith

theorem logTupleRange_le_pathVariation68 (k : ℕ) (a : ℝ) (y : Fin k → ℝ) :
    logTupleRange k (Fin.cons a y) ≤ 2*pathVariation68 k a a y := by
  have hb (j : Fin (k+1)) : |(Fin.cons a y : Fin (k+1) → ℝ) j-a| ≤ pathVariation68 k a a y := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa only [Fin.cons_zero, sub_self, abs_zero] using pathVariation68_nonneg k a a y
    · simpa only [Fin.cons_succ, abs_sub_comm] using pathVariation68_vertex k a a y i
  have hu : logTupleRoot .left k (Fin.cons a y) ≤ a+pathVariation68 k a a y := by
    apply Finset.sup'_le Finset.univ_nonempty
    intro j _
    linarith [(abs_le.mp (hb j)).2]
  have hl : a-pathVariation68 k a a y ≤ logTupleRoot .right k (Fin.cons a y) := by
    apply Finset.le_inf' Finset.univ_nonempty
    intro j _
    linarith [(abs_le.mp (hb j)).1]
  unfold logTupleRange
  linarith

theorem logTupleRoot_continuous68 (side : Corner) (k : ℕ) : Continuous (logTupleRoot side k) := by
  cases side
  · exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)
  · exact Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)

theorem logTupleRange_continuous68 (k : ℕ) : Continuous (logTupleRange k) :=
  (logTupleRoot_continuous68 .left k).sub (logTupleRoot_continuous68 .right k)

theorem openPathWeight68_const_mul (p : ℝ → ℝ) (C : ℝ) (k : ℕ) (a b : ℝ) (y : Fin k → ℝ) :
    openPathWeight68 (fun x => C*p x) k a b y = C^(k+1)*openPathWeight68 p k a b y := by
  induction k generalizing a b with
  | zero => simp [openPathWeight68]
  | succ k ih => simp only [openPathWeight68, ih, pow_succ]; ring

theorem openPathWeight68_mono {p q : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x) (hpq : ∀ x, p x ≤ q x)
    (k : ℕ) (a b : ℝ) (y : Fin k → ℝ) : openPathWeight68 p k a b y ≤ openPathWeight68 q k a b y := by
  induction k generalizing a b with
  | zero => exact hpq _
  | succ k ih =>
    exact mul_le_mul (hpq _) (ih _ _ _) (openPathWeight68_nonneg hp _ _ _ _)
      ((hp _).trans (hpq _))

theorem openPathWeight68_exp (c : ℝ) (k : ℕ) (a b : ℝ) (y : Fin k → ℝ) :
    openPathWeight68 (fun x => Real.exp (-c*|x|)) k a b y =
      Real.exp (-c*pathVariation68 k a b y) := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    simp only [openPathWeight68, pathVariation68, ih, ← Real.exp_add]
    congr 1
    ring

end Luce.Section6
