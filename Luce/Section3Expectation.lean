import Luce.Section3Profile
import Luce.Section3Mean
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The deterministic expectation limit in Section 3

Right endpoints of the actual profile cells are used throughout.  The
integrability argument below implements the manuscript's truncation of an
unbounded profile using dominated convergence; no regularity of the profile
itself is added.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace Luce

/-- Right endpoint of the cell containing a positive location. -/
def profileGridEndpoint (n : ℕ) (x : ℝ) : ℝ :=
  (⌈x * (n + 1 : ℕ)⌉₊ : ℝ) / (n + 1 : ℕ)

lemma profileGridEndpoint_ge (n : ℕ) (x : ℝ) : x ≤ profileGridEndpoint n x := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
  exact Nat.le_ceil _

lemma profileGridEndpoint_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < profileGridEndpoint n x := hx.trans_le (profileGridEndpoint_ge n x)

lemma profileGridEndpoint_of_mem_cell (n : ℕ) (i : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioc ((i.val : ℝ) / (n + 1 : ℕ))
      (((i.val : ℝ) + 1) / (n + 1 : ℕ))) :
    profileGridEndpoint n x = ((i.val : ℝ) + 1) / (n + 1 : ℕ) := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hceil : ⌈x * (n + 1 : ℕ)⌉₊ = i.val + 1 := by
    apply le_antisymm
    · apply Nat.ceil_le.mpr
      simpa only [Nat.cast_add, Nat.cast_one] using (le_div_iff₀ hn).mp hx.2
    · apply Nat.succ_le_of_lt
      apply Nat.lt_ceil.mpr
      exact (div_lt_iff₀ hn).mp hx.1
  unfold profileGridEndpoint
  rw [hceil]
  simp only [Nat.cast_add, Nat.cast_one]

lemma tendsto_profileGridEndpoint {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => profileGridEndpoint n x) atTop (𝓝 x) := by
  exact (tendsto_nat_ceil_mul_div_atTop hx).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

lemma measurable_comp_profileGridEndpoint (n : ℕ) (h : ℝ → ℝ) :
    Measurable (fun x => h (profileGridEndpoint n x)) := by
  exact (measurable_of_countable (fun k : ℕ => h ((k : ℝ) / (n + 1 : ℕ)))).comp
    ((measurable_id.mul_const ((n + 1 : ℕ) : ℝ)).nat_ceil)

lemma measurable_profileGridEndpoint (n : ℕ) : Measurable (profileGridEndpoint n) :=
  measurable_comp_profileGridEndpoint n id

/-- The label sum, expressed as a function constant in its label parameters
on each cell, with an arbitrary rate profile in the last argument. -/
def profileGridKernel (n : ℕ) (α : ℝ) (c t f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 < x ∧ profileGridEndpoint n x ≤ α then
    c (profileGridEndpoint n x) * rateKernel (t (profileGridEndpoint n x)) (f x)
  else 0

lemma aestronglyMeasurable_profileGridKernel (n : ℕ) (α : ℝ) (c t : ℝ → ℝ)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f profileMeasure) :
    AEStronglyMeasurable (profileGridKernel n α c t f) profileMeasure := by
  have hset : MeasurableSet {x : ℝ | 0 < x ∧ profileGridEndpoint n x ≤ α} :=
    measurableSet_Ioi.inter (measurableSet_le (measurable_profileGridEndpoint n) measurable_const)
  have hc := (measurable_comp_profileGridEndpoint n c).aestronglyMeasurable (μ := profileMeasure)
  have ht := (measurable_comp_profileGridEndpoint n t).aestronglyMeasurable (μ := profileMeasure)
  have hbase : AEStronglyMeasurable (fun x => c (profileGridEndpoint n x) *
      rateKernel (t (profileGridEndpoint n x)) (f x)) profileMeasure := by
    exact hc.mul (hf.mul (Real.continuous_exp.comp_aestronglyMeasurable (ht.neg.mul hf)))
  apply (hbase.indicator hset).congr
  filter_upwards [] with x
  simp only [profileGridKernel, Set.indicator_apply, Set.mem_ofPred_eq]

lemma abs_profileGridKernel_le {n : ℕ} {α C : ℝ} {c t f : ℝ → ℝ}
    (hC : 0 ≤ C) (hc : ∀ y ∈ Icc (0 : ℝ) α, |c y| ≤ C)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) {x : ℝ} (hf : 0 ≤ f x) :
    |profileGridKernel n α c t f x| ≤ C * f x := by
  unfold profileGridKernel
  split_ifs with hx
  · have hy : profileGridEndpoint n x ∈ Icc (0 : ℝ) α :=
      ⟨(profileGridEndpoint_pos n hx.1).le, hx.2⟩
    rw [abs_mul, abs_of_nonneg (rateKernel_nonneg hf)]
    exact mul_le_mul (hc _ hy) (rateKernel_le (ht _ hy) hf)
      (rateKernel_nonneg hf) hC
  · simpa only [abs_zero] using (mul_nonneg hC hf)

lemma integrable_profileGridKernel {n : ℕ} {α C : ℝ} {c t f : ℝ → ℝ}
    (hC : 0 ≤ C) (hc : ∀ y ∈ Icc (0 : ℝ) α, |c y| ≤ C)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    (hf : Integrable f profileMeasure) (hf₀ : ∀ᵐ x ∂profileMeasure, 0 ≤ f x) :
    Integrable (profileGridKernel n α c t f) profileMeasure := by
  apply (hf.const_mul C).mono' (aestronglyMeasurable_profileGridKernel n α c t hf.1)
  filter_upwards [hf₀] with x hx
  exact abs_profileGridKernel_le hC hc ht hx

/-- The global one-Lipschitz bound in the rate is preserved with variable
cellwise times. This supplies the uniform L¹ error in lines 792–797. -/
lemma abs_profileGridKernel_sub_le {n : ℕ} {α C : ℝ} {c t f g : ℝ → ℝ}
    (hC : 0 ≤ C) (hc : ∀ y ∈ Icc (0 : ℝ) α, |c y| ≤ C)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) {x : ℝ}
    (hf : 0 ≤ f x) (hg : 0 ≤ g x) :
    |profileGridKernel n α c t f x - profileGridKernel n α c t g x| ≤
      C * |f x - g x| := by
  unfold profileGridKernel
  split_ifs with hx
  · have hy : profileGridEndpoint n x ∈ Icc (0 : ℝ) α :=
      ⟨(profileGridEndpoint_pos n hx.1).le, hx.2⟩
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (hc _ hy) (abs_rateKernel_sub_le (ht _ hy) hf hg)
      (abs_nonneg _) hC
  · simpa using mul_nonneg hC (abs_nonneg (f x - g x))

def profileLimitKernel (α : ℝ) (c t f : ℝ → ℝ) : ℝ → ℝ :=
  (Ioc (0 : ℝ) α).indicator (fun x => c x * rateKernel (t x) (f x))

lemma tendsto_profileGridKernel {α : ℝ} {c t f : ℝ → ℝ}
    (hc : ContinuousOn c (Icc (0 : ℝ) α)) (ht : ContinuousOn t (Icc (0 : ℝ) α))
    {x : ℝ} (hx : 0 < x) (hxa : x ≠ α) :
    Tendsto (fun n => profileGridKernel n α c t f x) atTop
      (𝓝 (profileLimitKernel α c t f x)) := by
  have hq := tendsto_profileGridEndpoint hx.le
  rcases lt_or_gt_of_ne hxa with hlt | hgt
  · have hc' := hc.continuousAt (Icc_mem_nhds hx hlt)
    have ht' := ht.continuousAt (Icc_mem_nhds hx hlt)
    have hr : Continuous (fun r : ℝ => rateKernel r (f x)) := by
      unfold rateKernel survivalKernel
      fun_prop
    have hlim := (hc'.tendsto.comp hq).mul (hr.tendsto (t x) |>.comp (ht'.tendsto.comp hq))
    have hevent : ∀ᶠ n in atTop, profileGridEndpoint n x ≤ α :=
      (hq.eventually (gt_mem_nhds hlt)).mono (fun _ h => h.le)
    simp only [profileLimitKernel, Set.indicator_of_mem (s := Ioc (0 : ℝ) α) ⟨hx, hlt.le⟩]
    apply hlim.congr'
    filter_upwards [hevent] with n hn
    simp only [profileGridKernel, hx, hn, and_self, if_true, Function.comp_apply]
  · have hnot (n : ℕ) : ¬profileGridEndpoint n x ≤ α :=
      not_le_of_gt (hgt.trans_le (profileGridEndpoint_ge n x))
    have hxnot : x ∉ Ioc (0 : ℝ) α := fun h => not_le_of_gt hgt h.2
    simp only [profileGridKernel, hnot, and_false, if_false, profileLimitKernel,
      Set.indicator_of_notMem hxnot]
    exact tendsto_const_nhds

lemma ae_tendsto_profileGridKernel {α : ℝ} {c t f : ℝ → ℝ}
    (hc : ContinuousOn c (Icc (0 : ℝ) α)) (ht : ContinuousOn t (Icc (0 : ℝ) α)) :
    ∀ᵐ x ∂profileMeasure, Tendsto (fun n => profileGridKernel n α c t f x) atTop
      (𝓝 (profileLimitKernel α c t f x)) := by
  have : NullSingletonClass profileMeasure := by unfold profileMeasure; infer_instance
  filter_upwards [ae_restrict_mem measurableSet_Ioo, profileMeasure.ae_ne α] with x hx hxa
  exact tendsto_profileGridKernel hc ht hx.1 hxa

/-- Integrability of the actual limiting diagonal-type integrand is proved,
so its real integral never uses a value assigned to a nonintegrable function. -/
lemma integrable_profileLimitKernel {α C : ℝ} {c t f : ℝ → ℝ}
    (hC : 0 ≤ C) (hc : ContinuousOn c (Icc (0 : ℝ) α))
    (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (hcC : ∀ y ∈ Icc (0 : ℝ) α, |c y| ≤ C)
    (ht₀ : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    (hf : Integrable f profileMeasure) (hf₀ : ∀ᵐ x ∂profileMeasure, 0 ≤ f x) :
    Integrable (profileLimitKernel α c t f) profileMeasure := by
  have hlim := ae_tendsto_profileGridKernel (f := f) hc ht
  apply (hf.const_mul C).mono'
  · exact aestronglyMeasurable_of_tendsto_ae _
      (fun n => aestronglyMeasurable_profileGridKernel n α c t hf.1) hlim
  · filter_upwards [hf₀, hlim] with x hx hxl
    exact le_of_tendsto hxl.norm (Eventually.of_forall fun n =>
      abs_profileGridKernel_le hC hcC ht₀ hx)

/-- Dominated convergence at the fixed limiting profile handles unbounded f
and the cells touching zero without a pointwise bound on f. -/
theorem tendsto_integral_profileGridKernel {α C : ℝ} {c t f : ℝ → ℝ}
    (hC : 0 ≤ C) (hc : ContinuousOn c (Icc (0 : ℝ) α))
    (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (hcC : ∀ y ∈ Icc (0 : ℝ) α, |c y| ≤ C)
    (ht₀ : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    (hf : Integrable f profileMeasure) (hf₀ : ∀ᵐ x ∂profileMeasure, 0 ≤ f x) :
    Tendsto (fun n => ∫ x, profileGridKernel n α c t f x ∂profileMeasure) atTop
      (𝓝 (∫ x, profileLimitKernel α c t f x ∂profileMeasure)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => C * f x)
    (fun n => aestronglyMeasurable_profileGridKernel n α c t hf.1) (hf.const_mul C)
  · intro n
    filter_upwards [hf₀] with x hx
    exact abs_profileGridKernel_le hC hcC ht₀ hx
  · exact ae_tendsto_profileGridKernel hc ht

/-- L¹ perturbation from the paper's actual step profiles to the limit,
uniformly over all right-endpoint times. -/
theorem ProfileLimit.tendsto_integral_gridKernel {w : WeightArray} {f c t : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : 0 ≤ α)
    (hc : ContinuousOn c (Icc (0 : ℝ) α)) (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht₀ : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) :
    Tendsto (fun n => ∫ x, profileGridKernel n α c t (stepProfile w (n + 1)) x
      ∂profileMeasure) atTop (𝓝 (∫ x, profileLimitKernel α c t f x ∂profileMeasure)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hC₀ : 0 ≤ C := (norm_nonneg (c 0)).trans (hC 0 ⟨le_rfl, hα⟩)
  have herr (n : ℕ) :
      |(∫ x, profileGridKernel n α c t (stepProfile w (n + 1)) x ∂profileMeasure) -
        ∫ x, profileGridKernel n α c t f x ∂profileMeasure| ≤
          C * ∫ x, |stepProfile w (n + 1) x - f x| ∂profileMeasure := by
    rw [← integral_sub
      (integrable_profileGridKernel hC₀ hC ht₀ (integrable_stepProfile w (n + 1))
        (Eventually.of_forall (stepProfile_nonneg w (n + 1))))
      (integrable_profileGridKernel hC₀ hC ht₀ hf.integrable hf.ae_nonneg),
      ← integral_const_mul]
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le ((integrable_stepProfile w (n + 1)).sub hf.integrable
      |>.abs.const_mul C)
    filter_upwards [hf.ae_nonneg] with x hx
    exact abs_profileGridKernel_sub_le hC₀ hC ht₀ (stepProfile_nonneg w (n + 1) x) hx
  have herror : Tendsto (fun n =>
      (∫ x, profileGridKernel n α c t (stepProfile w (n + 1)) x ∂profileMeasure) -
        ∫ x, profileGridKernel n α c t f x ∂profileMeasure) atTop (𝓝 0) := by
    apply squeeze_zero_norm herr
    simpa using (hf.tendsto_integral_abs_sub.comp (tendsto_add_atTop_nat 1)).const_mul C
  simpa using herror.add (tendsto_integral_profileGridKernel hC₀ hc ht hC ht₀
    hf.integrable hf.ae_nonneg)

private lemma profileGridKernel_step_eq_sum (w : WeightArray) (n : ℕ) (α : ℝ)
    (c t : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    profileGridKernel n α c t (stepProfile w (n + 1)) x =
      ∑ i : Fin (n + 1), if (i.val : ℝ) / (n + 1 : ℕ) < x ∧
        x ≤ ((i.val : ℝ) + 1) / (n + 1 : ℕ) then
          (if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α then
            c (((i.val : ℝ) + 1) / (n + 1 : ℕ)) *
              rateKernel (t (((i.val : ℝ) + 1) / (n + 1 : ℕ))) ((w (n + 1)).rate i)
          else 0) else 0 := by
  obtain ⟨i, hi⟩ := exists_profile_cell (Nat.succ_pos n) hx
  have hqi := profileGridEndpoint_of_mem_cell n i hi
  rw [Finset.sum_eq_single i]
  · have hi' : (i.val : ℝ) / (n + 1 : ℕ) < x ∧
        x ≤ ((i.val : ℝ) + 1) / (n + 1 : ℕ) := hi
    rw [if_pos hi']
    simp only [profileGridKernel, hx.1, true_and, hqi,
      stepProfile_eq_of_mem_Ioc w (n + 1) i hi]
  · intro j hj hji
    apply if_neg
    intro hjx
    have hqj := profileGridEndpoint_of_mem_cell n j hjx
    have hend := hqj.symm.trans hqi
    have hv : (j.val : ℝ) + 1 = (i.val : ℝ) + 1 := by
      have hmul := congrArg (fun r : ℝ => r * (n + 1 : ℕ)) hend
      simpa only [div_mul_cancel₀ _ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)] using hmul
    apply hji
    apply Fin.ext
    exact_mod_cast (show (j.val : ℝ) = i.val by linarith)
  · simp

/-- Exact normalized finite expectation sum. The last fractional cell is
included precisely when its right endpoint lies at or below α. -/
theorem integral_profileGridKernel_step (w : WeightArray) (n : ℕ) (α : ℝ)
    (c t : ℝ → ℝ) :
    (∫ x, profileGridKernel n α c t (stepProfile w (n + 1)) x ∂profileMeasure) =
      (∑ i : Fin (n + 1), if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α then
        c (((i.val : ℝ) + 1) / (n + 1 : ℕ)) *
          rateKernel (t (((i.val : ℝ) + 1) / (n + 1 : ℕ))) ((w (n + 1)).rate i)
      else 0) / (n + 1 : ℕ) := by
  classical
  let b : Fin (n + 1) → ℝ := fun i =>
    if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α then
      c (((i.val : ℝ) + 1) / (n + 1 : ℕ)) *
        rateKernel (t (((i.val : ℝ) + 1) / (n + 1 : ℕ))) ((w (n + 1)).rate i)
    else 0
  let H : Fin (n + 1) → ℝ → ℝ := fun i =>
    (Ioc ((i.val : ℝ) / (n + 1 : ℕ))
      (((i.val : ℝ) + 1) / (n + 1 : ℕ))).indicator (fun _ => b i)
  have heq : profileGridKernel n α c t (stepProfile w (n + 1)) =ᵐ[profileMeasure]
      (fun x => ∑ i, H i x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [profileGridKernel_step_eq_sum w n α c t ⟨hx.1, hx.2.le⟩]
    simp only [H, b, Set.indicator_apply, Set.mem_Ioc]
  rw [integral_congr_ae heq, integral_finsetSum]
  · change (∑ i : Fin (n + 1), ∫ x, H i x ∂profileMeasure) = (∑ i, b i) / (n + 1 : ℕ)
    simp only [H, integral_indicator_const _ measurableSet_Ioc, smul_eq_mul,
      section3_cell_real_measure]
    rw [← Finset.mul_sum]
    ring
  · intro i hi
    exact (integrable_const (b i)).indicator measurableSet_Ioc

lemma integral_profileLimitKernel_eq {α : ℝ} (hα : α < 1) (c t f : ℝ → ℝ) :
    (∫ x, profileLimitKernel α c t f x ∂profileMeasure) =
      ∫ x in Ioc (0 : ℝ) α, c x * rateKernel (t x) (f x) := by
  rw [profileLimitKernel, integral_indicator measurableSet_Ioc]
  change (∫ x, c x * rateKernel (t x) (f x)
    ∂((volume.restrict (Ioo (0 : ℝ) 1)).restrict (Ioc (0 : ℝ) α))) = _
  rw [Measure.restrict_restrict_of_subset
    (show Ioc (0 : ℝ) α ⊆ Ioo (0 : ℝ) 1 from fun x hx => ⟨hx.1, hx.2.trans_lt hα⟩)]

/-- Finiteness of the limiting weighted diagonal integral follows from the
original profile hypothesis and continuous coefficients on the bulk. -/
theorem ProfileLimit.integrable_expectation_limit
    {w : WeightArray} {f c t : ℝ → ℝ} (hf : ProfileLimit w f) {α : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hc : ContinuousOn c (Icc (0 : ℝ) α)) (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht₀ : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) :
    IntegrableOn (fun x => c x * rateKernel (t x) (f x)) (Ioc (0 : ℝ) α) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hC₀ : 0 ≤ C := (norm_nonneg (c 0)).trans (hC 0 ⟨le_rfl, hα₀⟩)
  have h := integrable_profileLimitKernel hC₀ hc ht hC ht₀ hf.integrable hf.ae_nonneg
  rw [profileLimitKernel, integrable_indicator_iff measurableSet_Ioc] at h
  change Integrable (fun x => c x * rateKernel (t x) (f x))
    ((volume.restrict (Ioo (0 : ℝ) 1)).restrict (Ioc (0 : ℝ) α)) at h
  rwa [Measure.restrict_restrict_of_subset
    (show Ioc (0 : ℝ) α ⊆ Ioo (0 : ℝ) 1 from fun x hx => ⟨hx.1, hx.2.trans_lt hα₁⟩)] at h

/-- The deterministic expectation limit (lines 781–797), for arbitrary
continuous coefficient and nonnegative continuous arrival-time functions.
There is no boundedness or continuity assumption on the limiting profile.
Taking `c x = g x / D(t x)` recovers the expression in the manuscript. -/
theorem ProfileLimit.deterministic_expectation_limit
    {w : WeightArray} {f c t : ℝ → ℝ} (hf : ProfileLimit w f) {α : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hc : ContinuousOn c (Icc (0 : ℝ) α)) (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht₀ : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) :
    Tendsto (fun n =>
      (∑ i : Fin (n + 1), if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α then
        c (((i.val : ℝ) + 1) / (n + 1 : ℕ)) *
          rateKernel (t (((i.val : ℝ) + 1) / (n + 1 : ℕ))) ((w (n + 1)).rate i)
      else 0) / (n + 1 : ℕ)) atTop
      (𝓝 (∫ x in Ioc (0 : ℝ) α, c x * rateKernel (t x) (f x))) := by
  simpa only [integral_profileGridKernel_step, integral_profileLimitKernel_eq hα₁] using
    hf.tendsto_integral_gridKernel hα₀ hc ht ht₀

end Luce
