import Luce.Section6CriticalReferenceSum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

def criticalLower (n : ℕ) : ℕ := Nat.ceil (Real.sqrt (n : ℝ))
def criticalUpper (eps : ℝ) (n : ℕ) : ℕ := Nat.floor (eps*n)

/-- Fixed cutoffs with a square-root lower endpoint suffice for the
critical fixed-point approximation. -/
theorem critical_cutoffs_eventually {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∀ᶠ n : ℕ in atTop,
      4 ≤ criticalLower n ∧ criticalLower n ≤ criticalUpper eps n ∧
      criticalUpper eps n ≤ n ∧
      (n : ℝ) ≤ (criticalLower n : ℝ)^2 ∧
      Real.log (criticalLower n : ℝ) ≤ (3/4 : ℝ)*Real.log n ∧
      eps*n/2 ≤ (criticalUpper eps n : ℝ) ∧
      (criticalUpper eps n : ℝ) ≤ eps*n ∧ 1 ≤ Real.log (n : ℝ) := by
  have hnlim : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hs := Real.tendsto_sqrt_atTop.comp hnlim
  have hl := Real.tendsto_log_atTop.comp hnlim
  filter_upwards [hs.eventually_ge_atTop (max 4 (4/eps)),
    hl.eventually_ge_atTop (max 1 (4*Real.log 2))] with n hsn hln
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hs4 : 4 ≤ Real.sqrt (n : ℝ) := (le_max_left _ _).trans hsn
  have hse : 4/eps ≤ Real.sqrt (n : ℝ) := (le_max_right _ _).trans hsn
  have hsq := Real.sq_sqrt hn0
  have hnp : (0 : ℝ) < n := by nlinarith
  have hsn0 : 0 < Real.sqrt (n : ℝ) := by linarith
  have hsn1 : 1 ≤ Real.sqrt (n : ℝ) := by linarith
  have hAl := Nat.le_ceil (Real.sqrt (n : ℝ))
  have hAu := (Nat.ceil_lt_add_one (Real.sqrt_nonneg (n : ℝ))).le
  have hBl := Nat.lt_floor_add_one (eps*n)
  have hBu := Nat.floor_le (mul_nonneg heps.le hn0)
  have hAe : (criticalLower n : ℝ) ≤ eps*n/2 := by
    change (⌈Real.sqrt (n : ℝ)⌉₊ : ℝ) ≤ _
    have he := (div_le_iff₀ heps).mp hse
    have ht := mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg (n : ℝ))
    nlinarith
  have he2 : 2 ≤ eps*(n : ℝ) := by
    have : (4 : ℝ) ≤ criticalLower n := hs4.trans hAl
    linarith
  have hBhalf : eps*n/2 ≤ (criticalUpper eps n : ℝ) := by
    dsimp [criticalUpper]
    push_cast at hBl
    linarith
  refine ⟨?_,?_,?_,?_,?_,hBhalf,hBu,(le_max_left _ _).trans hln⟩
  · exact_mod_cast hs4.trans hAl
  · exact_mod_cast hAe.trans hBhalf
  · exact_mod_cast hBu.trans (mul_le_of_le_one_left hn0 heps1.le)
  · dsimp [criticalLower]
    nlinarith [sq_nonneg ((⌈Real.sqrt (n : ℝ)⌉₊ : ℝ)-Real.sqrt (n : ℝ))]
  · have hA2 : (criticalLower n : ℝ) ≤ 2*Real.sqrt (n : ℝ) := by
      dsimp [criticalLower]
      linarith
    have hAp : (0 : ℝ) < criticalLower n := hsn0.trans_le hAl
    have hh := Real.log_le_log hAp hA2
    rw [Real.log_mul (by norm_num) hsn0.ne',Real.log_sqrt hn0] at hh
    have := (le_max_right _ _).trans hln
    dsimp only [Function.comp_apply] at this
    linarith

end Luce.Section6
