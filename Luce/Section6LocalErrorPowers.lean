import Luce.Section6QuarterWindow
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
namespace Luce.Section6

def localPowerError (kappa n a h : ℝ) : ℝ :=
  (min a h)^(-kappa)+(max a h/n)^kappa

theorem localPowerError_nonneg {kappa n a h : ℝ} (hn : 0 < n) (ha : 0 < a) (hh : 0 < h) :
    0 ≤ localPowerError kappa n a h := by unfold localPowerError; positivity

theorem local_error_powers {rho kappa n a h : ℝ}
    (hn : 0 < n) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (hk : 0 < kappa) (hkquarter : kappa ≤ 1/4) (hkrho : kappa ≤ rho)
    (hsmall : max a h/n ≤ 1) :
    h^(-(1/4 : ℝ)) ≤ localPowerError kappa n a h ∧
    1/h ≤ localPowerError kappa n a h ∧
    h^(-(1/4 : ℝ))+crossDepthError rho n a h ≤ 2*localPowerError kappa n a h := by
  have hm1 : 1 ≤ min a h := le_min ha hh
  have hm0 : 0 < min a h := zero_lt_one.trans_le hm1
  have hh0 : 0 < h := zero_lt_one.trans_le hh
  have hp := Real.rpow_le_rpow_of_exponent_le hh (show -(1/4 : ℝ) ≤ -kappa by linarith)
  have hmin : h^(-kappa) ≤ (min a h)^(-kappa) :=
    Real.rpow_le_rpow_of_nonpos hm0 (min_le_right _ _) (neg_nonpos.mpr hk.le)
  have htime : h^(-(1/4 : ℝ)) ≤ (min a h)^(-kappa) := hp.trans hmin
  have hinv : 1/min a h ≤ (min a h)^(-kappa) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hmacro : (max a h/n)^rho ≤ (max a h/n)^kappa :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) hsmall hkrho
  have hmacro0 : 0 ≤ (max a h/n)^kappa := by positivity
  have htime' : h^(-(1/4 : ℝ)) ≤ localPowerError kappa n a h :=
    htime.trans (le_add_of_nonneg_right hmacro0)
  refine ⟨htime', ?_, ?_⟩
  · exact ((one_div_le_one_div_of_le hm0 (min_le_right _ _)).trans hinv).trans
      (le_add_of_nonneg_right hmacro0)
  · unfold crossDepthError localPowerError
    linarith only [htime, hinv, hmacro, hmacro0]

/-- Taking a square root of a union bound keeps a sum of individual
quarter-power errors, including an empty family. -/
theorem sqrt_sum_le_sum_sqrt {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∑ i, f i) ≤ ∑ i, Real.sqrt (f i) := by
  have hb := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => Real.sqrt (f i)) (fun i _ => Real.sqrt_nonneg _)
  simp only [Real.sq_sqrt (hf _)] at hb
  exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq (Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)))

theorem localPowerError_interval {kappa n a h A B : ℝ}
    (hk : 0 < kappa) (hn : 0 < n) (hA : 0 < A)
    (hAa : A ≤ a) (hAh : A ≤ h) (haB : a ≤ B) (hhB : h ≤ B) :
    localPowerError kappa n a h ≤ A^(-kappa)+(B/n)^kappa := by
  apply add_le_add
  · exact Real.rpow_le_rpow_of_nonpos hA (le_min hAa hAh) (neg_nonpos.mpr hk.le)
  · exact Real.rpow_le_rpow (div_nonneg (hA.le.trans (hAa.trans (le_max_left _ _))) hn.le)
      (div_le_div_of_nonneg_right (max_le haB hhB) hn.le) hk.le

/-- The interval clause quantifies over arbitrary B for an empty marked
family. Small positive exponents keep the real power nonnegative even
when that otherwise unconstrained B is negative. -/
theorem small_rpow_nonneg {kappa : ℝ} (hk : 0 ≤ kappa) (hkhalf : kappa ≤ 1/2) (x : ℝ) :
    0 ≤ x^kappa := by
  by_cases hx : 0 ≤ x
  · exact Real.rpow_nonneg hx _
  · rw [Real.rpow_def_of_neg (lt_of_not_ge hx)]
    apply mul_nonneg (Real.exp_pos _).le
    apply Real.cos_nonneg_of_mem_Icc
    have hl := mul_nonneg hk Real.pi_pos.le
    have hh := mul_le_mul_of_nonneg_right hkhalf Real.pi_pos.le
    constructor <;> linarith only [hl, hh, Real.pi_pos]

end Luce.Section6
