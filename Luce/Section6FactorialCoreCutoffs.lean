import Luce.Section6IdealCoreGrowth

noncomputable section
open Filter
open scoped Topology
namespace Luce.Section6

theorem factorial_core_error_inputs {n A B : ℕ} (hn : 0 < n) (hA : 1 ≤ A) (hAB : A ≤ B)
    (hB : (B : ℝ) ≤ (n : ℝ)/(A : ℝ)) :
    0 ≤ (B : ℝ)/(n : ℝ) ∧ (B : ℝ)/(n : ℝ) ≤ 1/(A : ℝ) ∧
      1 ≤ 1+Real.log ((B : ℝ)/A) ∧ 1+Real.log ((B : ℝ)/A) ≤ 1+Real.log (n : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hA0 : (0 : ℝ) < A := zero_lt_one.trans_le hA1
  have hABR : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hB0 : (0 : ℝ) < B := hA0.trans_le hABR
  refine ⟨div_nonneg hB0.le hnR.le, ?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ hnR hA0).mpr
    have hh := (le_div_iff₀ hA0).mp hB
    linarith
  · have hh := Real.log_nonneg ((one_le_div hA0).mpr hABR)
    linarith
  · have hBn : (B : ℝ) ≤ n := hB.trans (div_le_self hnR.le hA1)
    have hh := Real.log_le_log (div_pos hB0 hA0) ((div_le_self hB0.le hA1).trans hBn)
    linarith

theorem ideal_core_lower_tendsto : Tendsto idealCoreLower atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp (Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)))

theorem ideal_core_upper_le_div (n : ℕ) :
    (idealCoreUpper n : ℝ) ≤ (n : ℝ)/(idealCoreLower n : ℝ) :=
  Nat.floor_le (by positivity)

theorem ideal_core_upper_le_population (n : ℕ) : idealCoreUpper n ≤ n := by
  have hA : (1 : ℝ) ≤ idealCoreLower n := by exact_mod_cast idealCoreLower_pos68 n
  have h := (ideal_core_upper_le_div n).trans
    (div_le_self (Nat.cast_nonneg n) hA)
  exact_mod_cast h

theorem ideal_core_nonempty_eventually : ∀ᶠ n : ℕ in atTop, idealCoreLower n ≤ idealCoreUpper n := by
  filter_upwards [idealCoreLower_log_sublinear68 (show (0 : ℝ) < 1/2 by norm_num),
    eventually_ge_atTop 1] with n hlog hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : (0 : ℝ) < idealCoreLower n := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (idealCoreLower_pos68 n)
  have hsq : (idealCoreLower n : ℝ)^2 ≤ (n : ℝ) := by
    apply (Real.log_le_log_iff (pow_pos hA 2) hn0).mp
    rw [Real.log_pow]
    norm_num
    linarith
  apply Nat.le_floor
  apply (le_div_iff₀ hA).mpr
  nlinarith

/-- All cutoffs required by the local law and the separation of endpoint
cores follow from the manuscript's cutoffs. -/
theorem ideal_core_eventual_domain (h0 : ℕ) {delta : ℝ} (hd : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ h0 ≤ idealCoreLower n ∧
      idealCoreLower n ≤ idealCoreUpper n ∧
      2*idealCoreUpper n < n+1 ∧ (idealCoreUpper n : ℝ) ≤ delta*(n : ℝ) := by
  have hAreal : Tendsto (fun n => (idealCoreLower n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ideal_core_lower_tendsto
  filter_upwards [eventually_ge_atTop 2, ideal_core_lower_tendsto.eventually_ge_atTop h0,
    ideal_core_lower_tendsto.eventually_ge_atTop 3, ideal_core_nonempty_eventually,
    hAreal.eventually_ge_atTop (1/delta)] with n hn hh0 h3 hAB hdA
  have hA : (0 : ℝ) < idealCoreLower n := by exact_mod_cast (show 0 < idealCoreLower n by omega)
  have hB := (le_div_iff₀ hA).mp (ideal_core_upper_le_div n)
  have hsep : 2*idealCoreUpper n < n+1 := by
    have h3R : (3 : ℝ) ≤ idealCoreLower n := by exact_mod_cast h3
    have hmul : (2 : ℝ)*(idealCoreUpper n : ℝ) ≤ n := by
      nlinarith [show (0 : ℝ) ≤ idealCoreUpper n by positivity]
    have hmulN : 2*idealCoreUpper n ≤ n := by exact_mod_cast hmul
    omega
  refine ⟨hn, hh0, hAB, hsep, ?_⟩
  have hAd : 1 ≤ delta*(idealCoreLower n : ℝ) := by
    have h := (div_le_iff₀ hd).mp hdA
    nlinarith
  have hnon := mul_nonneg (Nat.cast_nonneg (idealCoreUpper n)) (sub_nonneg.mpr hAd)
  nlinarith [mul_le_mul_of_nonneg_left hB hd.le]

end Luce.Section6
