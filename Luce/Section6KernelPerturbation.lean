import Luce.Section6InactiveBounds
import Luce.Section3ProfileKernels

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

/-- Rate perturbations retain the decay at a common lower rate. -/
theorem survivalKernel_sub_bound_with_decay {t a b lower : ℝ}
    (ht : 0 ≤ t) (ha : lower ≤ a) (hb : lower ≤ b) :
    |survivalKernel t a - survivalKernel t b| ≤
      (t * survivalKernel t lower) * |a-b| := by
  have h := (convex_Ici lower).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_survivalKernel t x).hasDerivWithinAt)
    (C := t * survivalKernel t lower) (fun x hx => ?_) hb ha
  · simpa only [Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg ht,
      abs_of_pos (survivalKernel_pos t x)]
    apply mul_le_mul_of_nonneg_left _ ht
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr ht)

theorem rateKernel_sub_bound_with_decay {t a b lower upper : ℝ}
    (ht : 0 ≤ t) (hl : 0 ≤ lower) (ha : a ∈ Icc lower upper) (hb : b ∈ Icc lower upper) :
    |rateKernel t a - rateKernel t b| ≤
      ((1+t*upper) * survivalKernel t lower) * |a-b| := by
  have h := (convex_Icc lower upper).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_rateKernel t x).hasDerivWithinAt)
    (C := (1+t*upper) * survivalKernel t lower) (fun x hx => ?_) hb ha
  · simpa only [Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (survivalKernel_pos t x)]
    have hx0 : 0 ≤ x := hl.trans hx.1
    have hxU : 1+t*x ≤ 1+t*upper := by nlinarith [hx.2]
    have habs : |1-t*x| ≤ 1+t*x := by
      rw [abs_le]
      constructor <;> nlinarith [mul_nonneg ht hx0]
    have hexp : survivalKernel t x ≤ survivalKernel t lower := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hx.1 (neg_nonpos.mpr ht)
    exact mul_le_mul (habs.trans hxU) hexp (survivalKernel_pos _ _).le
      (by nlinarith [mul_nonneg ht (hl.trans hx.1 |>.trans hx.2)])

/-- Convert the literal relative expansion into its absolute power error.
The constant is obtained from big-O; it is not an additional hypothesis. -/
theorem PowerExpansion.absolute_error_bound {f : ℝ → ℝ} {c exponent eta : ℝ}
    (h : PowerExpansion f c exponent eta) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ),
      |f s - c*s^exponent| ≤ C*s^(exponent+eta) := by
  obtain ⟨C, hC, hb⟩ := h.exists_pos
  refine ⟨C*c, mul_pos hC hc, ?_⟩
  filter_upwards [hb.bound, self_mem_nhdsWithin] with s hs hs0
  have hp : 0 < c*s^exponent := mul_pos hc (Real.rpow_pos_of_pos hs0 _)
  have he : |f s - c*s^exponent| = |f s / (c*s^exponent)-1| * (c*s^exponent) := by
    have heq : (f s / (c*s^exponent)-1)*(c*s^exponent) = f s-c*s^exponent := by
      rw [sub_mul, div_mul_cancel₀ _ hp.ne', one_mul]
    calc
      _ = |(f s / (c*s^exponent)-1)*(c*s^exponent)| := congrArg abs heq.symm
      _ = _ := by rw [abs_mul, abs_of_pos hp]
  rw [he]
  have hb' : |f s / (c*s^exponent)-1| ≤ C*s^eta := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hs0 eta)] using hs
  calc
    _ ≤ (C*s^eta)*(c*s^exponent) := mul_le_mul_of_nonneg_right hb' hp.le
    _ = (C*c)*s^(exponent+eta) := by rw [Real.rpow_add hs0]; ring

/-- Uniform in nonnegative time, with the exponential envelope retained.
This is the perturbation step in the proof of sp-populations. -/
theorem PowerExpansion.kernel_perturbation_bounds {f : ℝ → ℝ} {c exponent eta : ℝ}
    (h : PowerExpansion f c exponent eta) (hc : 0 < c) (he : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ t : ℝ, 0 ≤ t →
      |survivalKernel t (f s) - survivalKernel t (c*s^exponent)| ≤
        C*t*s^(exponent+eta)*survivalKernel t ((c/2)*s^exponent) ∧
      |rateKernel t (f s) - rateKernel t (c*s^exponent)| ≤
        C*s^(exponent+eta)*(1+t*(2*c*s^exponent))*survivalKernel t ((c/2)*s^exponent) := by
  obtain ⟨C, hC, herr⟩ := h.absolute_error_bound hc
  refine ⟨C, hC, ?_⟩
  filter_upwards [herr, h.eventually_comparable hc he, self_mem_nhdsWithin]
    with s hs hb hs0
  intro t ht
  have hp := (Real.rpow_pos_of_pos hs0 exponent)
  have hl : 0 ≤ (c/2)*s^exponent := by positivity
  have hbase : (c/2)*s^exponent ≤ c*s^exponent := by nlinarith
  have ha : f s ∈ Icc ((c/2)*s^exponent) (2*c*s^exponent) := by
    exact ⟨hb.1, hb.2.trans (by nlinarith)⟩
  have hb' : c*s^exponent ∈ Icc ((c/2)*s^exponent) (2*c*s^exponent) := by
    exact ⟨hbase, by nlinarith⟩
  constructor
  · calc
      _ ≤ (t*survivalKernel t ((c/2)*s^exponent))*|f s-c*s^exponent| :=
        survivalKernel_sub_bound_with_decay ht ha.1 hbase
      _ ≤ (t*survivalKernel t ((c/2)*s^exponent))*(C*s^(exponent+eta)) :=
        mul_le_mul_of_nonneg_left hs (mul_nonneg ht (survivalKernel_pos _ _).le)
      _ = _ := by ring
  · calc
      _ ≤ ((1+t*(2*c*s^exponent))*survivalKernel t ((c/2)*s^exponent))*
          |f s-c*s^exponent| := rateKernel_sub_bound_with_decay ht hl ha hb'
      _ ≤ ((1+t*(2*c*s^exponent))*survivalKernel t ((c/2)*s^exponent))*
          (C*s^(exponent+eta)) := mul_le_mul_of_nonneg_left hs (by
            apply mul_nonneg _ (survivalKernel_pos _ _).le
            positivity)
      _ = _ := by ring

end Luce.Section6
