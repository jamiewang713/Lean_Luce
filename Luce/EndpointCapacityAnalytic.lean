import Luce.Endpoint
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Analytic ingredients of the block capacity bound. All positivity and
cutoff premises here are local mathematical premises of the block lemma,
not new assumptions on a triangular array. -/
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
namespace Luce

def endpointQ (x : ℝ) : ℝ := -Real.log (1 - Real.exp (-x))

theorem endpointQ_pos {x : ℝ} (hx : 0 < x) : 0 < endpointQ x := by
  apply neg_pos.mpr
  apply Real.log_neg
  · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
  · linarith [Real.exp_pos (-x)]

theorem endpointQ_antitone : AntitoneOn endpointQ (Ioi 0) := by
  intro x hx y hy hxy
  apply neg_le_neg
  apply Real.log_le_log
  · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
  · have := Real.exp_le_exp.mpr (neg_le_neg hxy)
    linarith

theorem exp_neg_le_endpointQ {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ endpointQ x := by
  have h := Real.log_le_sub_one_of_pos
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)))
  unfold endpointQ
  linarith

theorem endpointQ_le_two_exp {x : ℝ} (hx : Real.exp (-x) ≤ 1 / 2) :
    endpointQ x ≤ 2 * Real.exp (-x) := by
  have hpos : 0 < 1 - Real.exp (-x) := by linarith [Real.exp_pos (-x)]
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hi : (1 - Real.exp (-x))⁻¹ - 1 ≤ 2 * Real.exp (-x) := by
    rw [inv_eq_one_div]
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hpos).mpr
    nlinarith [Real.exp_pos (-x)]
  unfold endpointQ
  linarith

theorem hasDerivAt_log_one_sub_exp {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.log (1 - Real.exp (-a * s)))
      (a / (Real.exp (a * t) - 1)) t := by
  have hne : 1 - Real.exp (-a * t) ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  have h := (((hasDerivAt_id t).const_mul (-a)).exp.const_sub 1).log hne
  simp only [id_eq, mul_one] at h
  convert h using 1
  rw [show -a * t = -(a * t) by ring, Real.exp_neg]
  have he : Real.exp (a * t) ≠ 0 := (Real.exp_pos _).ne'
  have he1 : Real.exp (a * t) - 1 ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos ha ht))
  field_simp
  <;> ring

theorem tendsto_log_one_sub_exp (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => Real.log (1 - Real.exp (-a * t))) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha))
  have hh : Tendsto (fun t : ℝ => 1 - Real.exp (-a * t)) atTop (𝓝 1) := by
    simpa only [sub_zero] using he.const_sub 1
  simpa only [Real.log_one, Function.comp_def] using
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hh

/-- Exact late-time kernel integral in the manuscript's block bound. -/
theorem integral_capacity_kernel {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    (∫ t in Ioi s, a / (Real.exp (a * t) - 1)) = endpointQ (a * s) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t (ht : t ∈ Ici s) => hasDerivAt_log_one_sub_exp ha (hs.trans_le ht))
    (fun t (ht : t ∈ Ioi s) => div_nonneg ha.le
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg ha.le (hs.trans ht).le))))
    (tendsto_log_one_sub_exp a ha)
  simpa only [zero_sub, endpointQ, neg_mul] using h

theorem integrable_capacity_kernel {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    IntegrableOn (fun t => a / (Real.exp (a * t) - 1)) (Ioi s) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t (ht : t ∈ Ici s) => hasDerivAt_log_one_sub_exp ha (hs.trans_le ht))
    (fun t (ht : t ∈ Ioi s) => div_nonneg ha.le
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg ha.le (hs.trans ht).le))))
    (tendsto_log_one_sub_exp a ha)

/-- Monotonicity in the rate, valid at every positive time. This has no
late-time threshold of the form `a*t ≥ 1`. -/
theorem capacity_kernel_antitone {t : ℝ} (ht : 0 < t) :
    AntitoneOn (fun a : ℝ => a / (Real.exp (a * t) - 1)) (Ioi 0) := by
  let d (a : ℝ) := (Real.exp (a * t) - 1 - a * (Real.exp (a * t) * t)) /
    (Real.exp (a * t) - 1) ^ 2
  have hd (a : ℝ) (ha : 0 < a) :
      HasDerivAt (fun a : ℝ => a / (Real.exp (a * t) - 1)) (d a) a := by
    have hne : Real.exp (a * t) - 1 ≠ 0 :=
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos ha ht))).ne'
    convert! (hasDerivAt_id a).div
      (((hasDerivAt_id a).mul_const t).exp.sub_const 1) hne using 1 <;> simp [d]
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun a ha => (hd a ha).continuousAt.continuousWithinAt)
    (fun a ha => (hd a (by simpa using ha)).differentiableAt.differentiableWithinAt)
  intro a ha
  rw [(hd a (by simpa using ha)).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(a * t)))
    (Real.exp_pos (a * t)).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith

/-- The quadratic exponential estimate needed for the exact Chernoff
exponent in the manuscript's block proposition. -/
theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hd (y : ℝ) : HasDerivAt
      (fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y))
      (-1 + y + Real.exp (-y)) y := by
    convert! (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub ((hasDerivAt_id y).neg.exp) using 1 <;>
      simp <;> ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun y => by
    change 0 ≤ -1 + y + Real.exp (-y)
    have := Real.add_one_le_exp (-y)
    linarith)
  have h := hm hx
  simp only [neg_zero, Real.exp_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    sub_zero, add_zero, sub_self] at h
  linarith

end Luce
