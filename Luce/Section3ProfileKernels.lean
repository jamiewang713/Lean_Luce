import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# The profile kernels

Analytic estimates used in Section 3 of `fixed_points.tex`.  In particular the
remaining-rate kernel is globally one-Lipschitz in its rate, including at time
zero.  Integrating these estimates gives the uniform-in-time L¹ comparison
needed for the deterministic part of the race law.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Luce

def survivalKernel (t a : ℝ) : ℝ := Real.exp (-t * a)

def rateKernel (t a : ℝ) : ℝ := a * survivalKernel t a

lemma survivalKernel_pos (t a : ℝ) : 0 < survivalKernel t a := Real.exp_pos _

lemma survivalKernel_le_one {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) :
    survivalKernel t a ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith

lemma rateKernel_nonneg {t a : ℝ} (ha : 0 ≤ a) : 0 ≤ rateKernel t a :=
  mul_nonneg ha (survivalKernel_pos t a).le

lemma rateKernel_le {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) : rateKernel t a ≤ a := by
  simpa [rateKernel] using mul_le_mul_of_nonneg_left (survivalKernel_le_one ht ha) ha

lemma survivalKernel_antitone_time {a : ℝ} (ha : 0 ≤ a) :
    Antitone (fun t => survivalKernel t a) := by
  intro s t hst
  apply Real.exp_le_exp.mpr
  nlinarith

lemma rateKernel_antitone_time {a : ℝ} (ha : 0 ≤ a) :
    Antitone (fun t => rateKernel t a) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left (survivalKernel_antitone_time ha hst) ha

lemma hasDerivAt_survivalKernel (t a : ℝ) :
    HasDerivAt (survivalKernel t) (-t * survivalKernel t a) a := by
  unfold survivalKernel
  simpa [survivalKernel, mul_comm] using (((hasDerivAt_id a).const_mul (-t)).exp)

lemma hasDerivAt_rateKernel (t a : ℝ) :
    HasDerivAt (rateKernel t) ((1 - t * a) * survivalKernel t a) a := by
  have h := (hasDerivAt_id a).mul (hasDerivAt_survivalKernel t a)
  have heq : (1 - t * a) * survivalKernel t a =
      1 * survivalKernel t a + a * (-t * survivalKernel t a) := by ring
  rw [heq]
  exact h

lemma abs_rateKernel_derivative_le_one {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) :
    |(1 - t * a) * survivalKernel t a| ≤ 1 := by
  have he := survivalKernel_le_one ht ha
  have hp := (survivalKernel_pos t a).le
  have hx : t * a * survivalKernel t a ≤ 1 := by
    have h := Real.mul_exp_neg_le_exp_neg_one (t * a)
    have h₁ : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have h₂ : t * a * survivalKernel t a ≤ Real.exp (-1) := by
      simpa [survivalKernel, neg_mul] using h
    exact h₂.trans h₁
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (mul_nonneg ht ha) hp]

theorem abs_rateKernel_sub_le {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |rateKernel t a - rateKernel t b| ≤ |a - b| := by
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_rateKernel t x).hasDerivWithinAt)
    (fun x hx => (show ‖(1 - t * x) * survivalKernel t x‖ ≤ (1 : ℝ) from
      abs_rateKernel_derivative_le_one ht hx)) hb ha
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem abs_survivalKernel_sub_le {t a b : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |survivalKernel t a - survivalKernel t b| ≤ t * |a - b| := by
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_survivalKernel t x).hasDerivWithinAt)
    (C := t) (fun x hx => ?_) hb ha
  · simpa only [Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg ht,
      abs_of_pos (survivalKernel_pos t x)]
    simpa using mul_le_mul_of_nonneg_left (survivalKernel_le_one ht hx) ht

section Integrals

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def profileH (μ : Measure Ω) (f : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ x, survivalKernel t (f x) ∂μ

def profileF (μ : Measure Ω) (f : Ω → ℝ) (t : ℝ) : ℝ := 1 - profileH μ f t

def profileD (μ : Measure Ω) (f : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ x, rateKernel t (f x) ∂μ

lemma integrable_rateKernel {f : Ω → ℝ} (hf : Integrable f μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => rateKernel t (f x)) μ := by
  apply hf.mono'
  · exact hf.aestronglyMeasurable.mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
        hf.aestronglyMeasurable)
  · filter_upwards [hf₀] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (rateKernel_nonneg hx)]
    exact rateKernel_le ht hx

lemma integrable_survivalKernel [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun x => survivalKernel t (f x)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable hf
  · filter_upwards [hf₀] with x hx
    simpa only [Real.norm_eq_abs, abs_of_pos (survivalKernel_pos t (f x))] using
      survivalKernel_le_one ht hx

/-- L¹ stability of the remaining-rate transform, uniformly for every nonnegative time. -/
theorem abs_profileD_sub_le {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) (hg₀ : ∀ᵐ x ∂μ, 0 ≤ g x) {t : ℝ} (ht : 0 ≤ t) :
    |profileD μ f t - profileD μ g t| ≤ ∫ x, |f x - g x| ∂μ := by
  rw [profileD, profileD, ← integral_sub (integrable_rateKernel hf hf₀ ht)
    (integrable_rateKernel hg hg₀ ht)]
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hf.sub hg).abs
  filter_upwards [hf₀, hg₀] with x hx hy
  exact abs_rateKernel_sub_le ht hx hy

/-- L¹ stability of the arrival transform on a bounded time interval. -/
theorem abs_profileF_sub_le [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) (hg₀ : ∀ᵐ x ∂μ, 0 ≤ g x)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    |profileF μ f t - profileF μ g t| ≤ T * ∫ x, |f x - g x| ∂μ := by
  have h : |profileH μ f t - profileH μ g t| ≤ t * ∫ x, |f x - g x| ∂μ := by
    rw [profileH, profileH, ← integral_sub
      (integrable_survivalKernel hf.aestronglyMeasurable hf₀ ht)
      (integrable_survivalKernel hg.aestronglyMeasurable hg₀ ht), ← integral_const_mul]
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le ((hf.sub hg).abs.const_mul t)
    filter_upwards [hf₀, hg₀] with x hx hy
    exact abs_survivalKernel_sub_le ht hx hy
  have heq : |profileF μ f t - profileF μ g t| = |profileH μ f t - profileH μ g t| := by
    have heq' : profileF μ f t - profileF μ g t = -(profileH μ f t - profileH μ g t) := by
      dsimp [profileF]
      ring
    rw [heq', abs_neg]
  rw [heq]
  exact h.trans (mul_le_mul_of_nonneg_right htT (integral_nonneg fun _ => abs_nonneg _))

/-- L¹ convergence implies uniform convergence of the deterministic remaining rate,
even on the entire nonnegative time axis. -/
theorem tendstoUniformlyOn_profileD {f : Ω → ℝ} {fn : ℕ → Ω → ℝ}
    (hf : Integrable f μ) (hfn : ∀ n, Integrable (fn n) μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) (hfn₀ : ∀ n, ∀ᵐ x ∂μ, 0 ≤ fn n x)
    (hL₁ : Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => profileD μ (fn n)) (profileD μ f) atTop (Ici 0) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hL₁.eventually (gt_mem_nhds hε)] with n hn t ht
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_profileD_sub_le (hfn n) hf (hfn₀ n) hf₀ ht).trans_lt hn

/-- The arrival transforms converge uniformly on every bounded time interval. -/
theorem tendstoUniformlyOn_profileF [IsFiniteMeasure μ] {f : Ω → ℝ} {fn : ℕ → Ω → ℝ}
    (hf : Integrable f μ) (hfn : ∀ n, Integrable (fn n) μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) (hfn₀ : ∀ n, ∀ᵐ x ∂μ, 0 ≤ fn n x)
    (hL₁ : Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0)) (T : ℝ) :
    TendstoUniformlyOn (fun n => profileF μ (fn n)) (profileF μ f) atTop (Icc 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hT : Tendsto (fun n => T * ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0) := by
    simpa using hL₁.const_mul T
  filter_upwards [hT.eventually (gt_mem_nhds hε)] with n hn t ht
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_profileF_sub_le (hfn n) hf (hfn₀ n) hf₀ ht.1 ht.2).trans_lt hn

/-- The mass of any shrinking cells vanishes under L¹-convergent profiles.
Choosing the cell containing a largest weight is the maximum-weight argument
in equation `eq:max-weight`; no fixed choice of cells is required. -/
theorem tendsto_setIntegral_of_L1_of_measure_tendsto_zero
    {f : Ω → ℝ} {fn : ℕ → Ω → ℝ} {cells : ℕ → Set Ω}
    (hf : Integrable f μ) (hfn : ∀ n, Integrable (fn n) μ)
    (hL₁ : Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0))
    (hcells : Tendsto (fun n => μ (cells n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in cells n, fn n x ∂μ) atTop (𝓝 0) := by
  have hbase := hf.tendsto_setIntegral_nhds_zero hcells
  have herr : Tendsto (fun n => (∫ x in cells n, fn n x ∂μ) -
      ∫ x in cells n, f x ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hL₁
    rw [← integral_sub (hfn n).integrableOn hf.integrableOn]
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun x => norm_nonneg (fn n x - f x)) (hfn n |>.sub hf).norm
  simpa using herr.add hbase

/-- A normalized weight represented as the mass of a shrinking profile cell is negligible. -/
theorem tendsto_normalized_weight_of_cells
    {f : Ω → ℝ} {fn : ℕ → Ω → ℝ} {cells : ℕ → Set Ω} {weights : ℕ → ℝ}
    (hf : Integrable f μ) (hfn : ∀ n, Integrable (fn n) μ)
    (hL₁ : Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0))
    (hcells : Tendsto (fun n => μ (cells n)) atTop (𝓝 0))
    (hweights : ∀ n, weights n / (n + 1 : ℕ) = ∫ x in cells n, fn n x ∂μ) :
    Tendsto (fun n => weights n / (n + 1 : ℕ)) atTop (𝓝 0) := by
  simp_rw [hweights]
  exact tendsto_setIntegral_of_L1_of_measure_tendsto_zero hf hfn hL₁ hcells

end Integrals
end Luce
