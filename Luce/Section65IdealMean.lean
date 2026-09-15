import Luce.Section65CoreScale
import Luce.Section65MeanAsymptotic
import Luce.Section6Lemma68
import Luce.Section6FactorialCoreCutoffs

noncomputable section
open Filter
open scoped Topology
namespace Luce.Section6

theorem core_log_ratio_error65 {n : ℕ} (hn : 1 ≤ n)
    (hAB : idealCoreLower n ≤ idealCoreUpper n) :
    |Real.log ((idealCoreUpper n : ℝ)/idealCoreLower n)-Real.log (n : ℝ)| ≤
      2*Real.log (idealCoreLower n : ℝ)+1 := by
  let A := idealCoreLower n
  let B := idealCoreUpper n
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast idealCoreLower_pos68 n
  have hA : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hB : (0 : ℝ) < B := hA.trans_le (by exact_mod_cast hAB)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hx : 1 ≤ (n : ℝ)/A :=
    hA1.trans ((show (A : ℝ) ≤ B by exact_mod_cast hAB).trans (ideal_core_upper_le_div n))
  have hf := (log_floor_errors_le_one68 hx).1
  change |Real.log (B : ℝ)-Real.log ((n : ℝ)/A)| ≤ 1 at hf
  have hlA : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg hA1
  change |Real.log ((B : ℝ)/A)-Real.log (n : ℝ)| ≤ 2*Real.log (A : ℝ)+1
  rw [Real.log_div hB.ne' hA.ne']
  rw [Real.log_div hn0.ne' hA.ne'] at hf
  have he : Real.log (B : ℝ)-Real.log (A : ℝ)-Real.log (n : ℝ) =
      (Real.log (B : ℝ)-(Real.log (n : ℝ)-Real.log (A : ℝ)))-2*Real.log (A : ℝ) := by ring
  rw [he]
  have htri := abs_sub (Real.log (B : ℝ)-(Real.log (n : ℝ)-Real.log (A : ℝ)))
    (2*Real.log (A : ℝ))
  rw [abs_of_nonneg (mul_nonneg (by norm_num) hlA)] at htri
  linarith

theorem meanApprox65_of_core_log_bound {μ : ℕ → ℝ} {β C D : ℝ}
    (h : ∀ᶠ n in atTop, |μ n-β*Real.log (n : ℝ)| ≤
      C*(1+Real.log (idealCoreLower n : ℝ))+
        D*((1+Real.log (n : ℝ))/(idealCoreLower n : ℝ))) : MeanApprox65 μ β := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hlog)
  have hA : Tendsto (fun n : ℕ => (1+Real.log (n : ℝ))/(idealCoreLower n : ℝ)) atTop (𝓝 0) := by
    simpa [Real.rpow_neg_one, div_eq_mul_inv] using core_error_tendsto65 1 (κ := 1) zero_lt_one
  have hlim := (one_add_log_core_lower_sqrt_tendsto65.const_mul C).add ((hA.mul hi).const_mul D)
  simp only [mul_zero, zero_add] at hlim
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _)) ?_ hlim
  filter_upwards [h,hlog.eventually_gt_atTop 0] with n hn hl
  simp only [Function.comp_apply, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hdiv := div_le_div_of_nonneg_right hn (Real.sqrt_nonneg (Real.log (n : ℝ)))
  exact hdiv.trans_eq (by ring)

theorem idealTrace_meanApprox65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (side : Corner)
    (ha : (cornerBehavior left right side).active) (k : ℕ) :
    MeanApprox65 (fun n => idealTrace side (cornerBehavior left right side) k
      (idealCoreLower n) (idealCoreUpper n))
      (cornerCoefficient side (cornerBehavior left right side) k) := by
  obtain ⟨C,D,hC,hD,M,hM,htrace⟩ := lemma68_total f left right hp side ha k
  let β := cornerCoefficient side (cornerBehavior left right side) k
  apply meanApprox65_of_core_log_bound (C := C+2*|β|) (D := D)
  filter_upwards [ideal_core_lower_tendsto.eventually_ge_atTop M,
    ideal_core_nonempty_eventually, eventually_ge_atTop 1] with n hAn hAB hn
  have hA := idealCoreLower_pos68 n
  have hA0 : (0 : ℝ) < idealCoreLower n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have h := htrace (idealCoreLower n) (idealCoreUpper n) hAn hAB
  have hlog := (factorial_core_error_inputs (by omega : 0 < n) hA hAB (ideal_core_upper_le_div n)).2.2.2
  have hf := div_le_div_of_nonneg_right hlog hA0.le
  have hlA := Real.log_natCast_nonneg (idealCoreLower n)
  have hcoef := mul_le_mul_of_nonneg_left (core_log_ratio_error65 hn hAB) (abs_nonneg β)
  rw [← abs_mul] at hcoef
  have htri := abs_add_le
    (idealTrace side (cornerBehavior left right side) k (idealCoreLower n) (idealCoreUpper n)-
      β*Real.log ((idealCoreUpper n : ℝ)/idealCoreLower n))
    (β*(Real.log ((idealCoreUpper n : ℝ)/idealCoreLower n)-Real.log (n : ℝ)))
  have he : idealTrace side (cornerBehavior left right side) k (idealCoreLower n) (idealCoreUpper n)-
      β*Real.log ((idealCoreUpper n : ℝ)/idealCoreLower n)+
        β*(Real.log ((idealCoreUpper n : ℝ)/idealCoreLower n)-Real.log (n : ℝ)) =
      idealTrace side (cornerBehavior left right side) k (idealCoreLower n) (idealCoreUpper n)-
        β*Real.log (n : ℝ) := by ring
  rw [he] at htri
  dsimp [β] at *
  nlinarith only [h,hcoef,htri,mul_nonneg hC.le hlA,
    mul_le_mul_of_nonneg_left hf hD.le,
    abs_nonneg (cornerCoefficient side (cornerBehavior left right side) k)]

theorem idealSpatialTrace_meanApprox65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (side : Corner)
    (ha : (cornerBehavior left right side).active) (k : ℕ) {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) :
    MeanApprox65 (fun n => idealSpatialTrace side (cornerBehavior left right side) k n a b)
      (cornerCoefficient side (cornerBehavior left right side) k*(b-a)) := by
  obtain ⟨C,κ,hC,hκ,K,N,hN,hbound⟩ := lemma68_spatial f left right hp side ha k a b ha0 hab hb1
  have he : RapidError65 (fun n => idealSpatialTrace side (cornerBehavior left right side) k n a b-
      cornerCoefficient side (cornerBehavior left right side) k*(b-a)*Real.log (n : ℝ)) :=
    rapidError65_of_core_bound hκ (eventually_atTop.mpr ⟨N,fun n hn => hbound n hn⟩)
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  simpa only [MeanApprox65,div_eq_mul_inv,mul_zero,Function.comp_apply] using he.tendsto.mul hi

end Luce.Section6
