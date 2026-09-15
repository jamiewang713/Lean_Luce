import Luce.EndpointShellCompatibility
import Luce.EndpointCapacityAnalytic
import Mathlib.Analysis.PSeries

/-! The square-root buffer. Every estimate is derived from the raw costs;
the buffered condition is not added to `EndpointShellAssumption`. -/
noncomputable section
open Real Set Filter
open scoped Topology BigOperators ENNReal
namespace Luce

/-- Pointwise splitting inequality, with `s = sqrt j`. -/
theorem buffer_exp_bound (b s : ℝ) (hs : 1 ≤ s) :
    Real.exp (-b * (s ^ 2 - s)) ≤
      Real.exp 1 * Real.exp (-b * s ^ 2) + Real.exp (1 - s) := by
  by_cases h : b * s ≤ 1
  · apply le_trans _ (le_add_of_nonneg_right (Real.exp_pos _).le)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  · have hmul' := mul_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h))) (sub_nonneg.mpr hs)
    apply le_trans _ (le_add_of_nonneg_left (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le)
    apply Real.exp_le_exp.mpr
    nlinarith

/-- The error sequence is genuinely summable, not an assumed envelope. -/
theorem summable_buffer_error : Summable (fun j : ℕ => Real.exp (1 - Real.sqrt j)) := by
  apply (summable_nat_add_iff 1).mp
  have hp : Summable (fun j : ℕ => (Real.exp 1 * 24) * (1 / ((j + 1 : ℕ) : ℝ) ^ 2)) :=
    (((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))).mul_left _)
  apply hp.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro j
  have hj : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hs := Real.pow_div_factorial_le_exp _ (Real.sqrt_nonneg ((j + 1 : ℕ) : ℝ)) 4
  have hs4 : (Real.sqrt ((j + 1 : ℕ) : ℝ)) ^ 4 = (((j + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hj.le]
  rw [hs4] at hs
  norm_num only [Nat.factorial] at hs
  have hbound : Real.exp (-Real.sqrt ((j + 1 : ℕ) : ℝ)) ≤
      24 / (((j + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (sq_pos_of_pos hj)]
    nlinarith
  rw [show 1 - Real.sqrt ((j + 1 : ℕ) : ℝ) =
    1 + -Real.sqrt ((j + 1 : ℕ) : ℝ) by ring, Real.exp_add]
  calc
    _ ≤ Real.exp 1 * (24 / (((j + 1 : ℕ) : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos 1).le
    _ = _ := by ring

/-- Exponential buffered costs are used only for j≥2, where the cutoff
is positive. Dropping finitely many indices has no effect on the tail limit. -/
def bufferedShellExpCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  if hj : 2 ≤ j then
    if h : (terminalShell n j).Nonempty then
      ENNReal.ofReal (Real.exp (-shellFloor w n j h * ((j : ℝ) - Real.sqrt j))) else 0
  else 0

def bufferedShellQCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  if hj : 2 ≤ j then
    if h : (terminalShell n j).Nonempty then
      ENNReal.ofReal (endpointQ (shellFloor w n j h * ((j : ℝ) - Real.sqrt j))) else 0
  else 0

theorem bufferedShellExpCost_le (w : WeightArray) (n j : ℕ) :
    bufferedShellExpCost w n j ≤ ENNReal.ofReal (Real.exp 1) * shellCost w n j +
      ENNReal.ofReal (Real.exp (1 - Real.sqrt j)) := by
  unfold bufferedShellExpCost
  split_ifs with hj h
  · have hs : 1 ≤ Real.sqrt (j : ℝ) := by
      apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg j)).mpr
      simpa using (show (1 : ℝ) ≤ j by exact_mod_cast (show 1 ≤ j by omega))
    have hb := buffer_exp_bound (shellFloor w n j h) (Real.sqrt j) hs
    rw [Real.sq_sqrt (Nat.cast_nonneg j)] at hb
    calc
      _ ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-shellFloor w n j h * (j : ℝ)) +
          Real.exp (1 - Real.sqrt j)) := ENNReal.ofReal_le_ofReal hb
      _ = _ := by rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (Real.exp_pos _).le]; simp only [shellCost, dif_pos h]
  · exact bot_le
  · exact bot_le

end Luce
