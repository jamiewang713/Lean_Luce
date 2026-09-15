import Luce.Section6LogCells
import Luce.Section6IdealTraceDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter
open scoped Topology
namespace Luce.Section6

theorem idealCoreLower_pos68 (n : ℕ) : 1 ≤ idealCoreLower n := by
  have h := Nat.le_ceil (Real.exp ((Real.log (n : ℝ))^(1/4 : ℝ)))
  have he := Real.exp_pos ((Real.log (n : ℝ))^(1/4 : ℝ))
  have : (0 : ℝ) < idealCoreLower n := lt_of_lt_of_le he h
  exact Nat.succ_le_of_lt (by exact_mod_cast this)

theorem idealCoreLower_log_sublinear68 {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, Real.log (idealCoreLower n : ℝ) ≤ e*Real.log (n : ℝ) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/4)).comp hlog
  filter_upwards [hpow.eventually (gt_mem_nhds (show (0 : ℝ) < e/2 by positivity)),
    hlog.eventually_ge_atTop (2*Real.log 2/e), hlog.eventually_gt_atTop 0] with n hp hn hn0
  let t := Real.log (n : ℝ)
  have ht : 0 < t := hn0
  have hsmall : t^(1/4 : ℝ) ≤ (e/2)*t := by
    have hid : t^(1/4 : ℝ) = t^(-(3/4 : ℝ))*t := by
      calc
        t^(1/4 : ℝ) = t^(-(3/4 : ℝ)+1) := by norm_num
        _ = t^(-(3/4 : ℝ))*t^((1 : ℝ)) := Real.rpow_add ht _ _
        _ = t^(-(3/4 : ℝ))*t := by rw [Real.rpow_one]
    rw [hid]
    exact mul_le_mul_of_nonneg_right hp.le ht.le
  have hexp : 1 ≤ Real.exp (t^(1/4 : ℝ)) :=
    Real.one_le_exp_iff.mpr (Real.rpow_nonneg ht.le _)
  have hceil : (idealCoreLower n : ℝ) ≤ 2*Real.exp (t^(1/4 : ℝ)) :=
    (Nat.ceil_lt_add_one (Real.exp_pos _).le).le.trans (by linarith)
  have hA : (0 : ℝ) < idealCoreLower n := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (idealCoreLower_pos68 n)
  have hupper := Real.log_le_log hA hceil
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hupper
  have hconst : Real.log 2 ≤ (e/2)*t := by
    have := (div_le_iff₀ he).mp hn
    dsimp [t]
    nlinarith
  dsimp [t] at hsmall hupper hconst
  linarith

theorem log_floor_errors68 {x : ℝ} (hx : 1 ≤ x) :
    |Real.log (⌊x⌋₊ : ℝ)-Real.log x| ≤ 1/(⌊x⌋₊ : ℝ) ∧
    |Real.log ((⌊x⌋₊+1 : ℕ) : ℝ)-Real.log x| ≤ 1/(⌊x⌋₊ : ℝ) := by
  have hm : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hmR : 0 < (⌊x⌋₊ : ℝ) := by exact_mod_cast hm
  have hx0 : 0 < x := by linarith
  have hlow := Real.log_le_log hmR (Nat.floor_le hx0.le)
  have hupp := Real.log_le_log hx0 (Nat.lt_succ_floor x).le
  have hwidth := (logCellWidth68_bounds hm).2
  change Real.log ((⌊x⌋₊+1 : ℕ) : ℝ)-Real.log (⌊x⌋₊ : ℝ) ≤ _ at hwidth
  constructor
  · rw [abs_of_nonpos (sub_nonpos.mpr hlow)]
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hupp)]
    linarith

theorem log_floor_errors_le_one68 {x : ℝ} (hx : 1 ≤ x) :
    |Real.log (⌊x⌋₊ : ℝ)-Real.log x| ≤ 1 ∧
    |Real.log ((⌊x⌋₊+1 : ℕ) : ℝ)-Real.log x| ≤ 1 := by
  have h := log_floor_errors68 hx
  have h1 : 1/(⌊x⌋₊ : ℝ) ≤ 1 := by
    apply (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (by exact_mod_cast (Nat.one_le_floor_iff x).mpr hx)).trans_eq
    norm_num
  exact ⟨h.1.trans h1, h.2.trans h1⟩

end Luce.Section6
