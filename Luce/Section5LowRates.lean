import Luce.Section5HighRates

/-!
# Scarcity of low-rate labels

Source: `fixed_points.tex:1174–1185`. The proportion of labels with rate
below δ tends uniformly to zero as δ tends to zero after n. This is proved
from L1 convergence and positivity of the limiting profile, with no extra
lower bound on all rates or regularity of the profile.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Luce
attribute [local instance] Classical.propDecidable

def lowRateDensity (w : WeightArray) (n : ℕ) (δ : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i : Fin n => (w n).rate i < δ)).card : ℝ) / n

lemma lowRateDensity_eq_integral (w : WeightArray) (n : ℕ) (δ : ℝ) :
    lowRateDensity w n δ = ∫ x,
      (if 0 < stepProfile w n x ∧ stepProfile w n x < δ then (1 : ℝ) else 0)
      ∂profileMeasure := by
  rw [integral_comp_stepProfile w n (fun a => if 0 < a ∧ a < δ then 1 else 0) (by simp)]
  simp [lowRateDensity, (w n).positive, Finset.sum_boole]

lemma integrable_lowProfile (w : WeightArray) (n : ℕ) (δ : ℝ) :
    Integrable (fun x => if 0 < stepProfile w n x ∧ stepProfile w n x < δ
      then (1 : ℝ) else 0) profileMeasure := by
  have hm : MeasurableSet {x : ℝ | 0 < stepProfile w n x ∧ stepProfile w n x < δ} :=
    (measurableSet_lt measurable_const (measurable_stepProfile w n)).inter
      (measurableSet_lt (measurable_stepProfile w n) measurable_const)
  have hg : Measurable (fun x : ℝ =>
      if 0 < stepProfile w n x ∧ stepProfile w n x < δ then (1 : ℝ) else 0) :=
    Measurable.ite hm measurable_const measurable_const
  apply Integrable.of_bound hg.aestronglyMeasurable 1
  filter_upwards [] with x
  split_ifs <;> norm_num

/-- Continuous triangular cutoffs shrink to zero at every positive profile
value. The limit's strict positivity is used precisely at this point. -/
lemma ProfileLimit.lowTriangle_tail {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) :
    Tendsto (fun K : ℕ => ∫ x, max (1 - K * f x) 0 ∂profileMeasure) atTop (𝓝 0) := by
  have hm (K : ℕ) : AEStronglyMeasurable
      (fun x => max (1 - K * f x) 0) profileMeasure :=
    (((integrable_const 1).sub (hf.integrable.const_mul (K : ℝ))).sup
      (integrable_const 0)).aestronglyMeasurable
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ)) hm (integrable_const 1)
  simp only [integral_zero] at h
  apply h
  · intro K
    filter_upwards [hf.ae_nonneg] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le _ zero_le_one
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) K) hx
    linarith
  · filter_upwards [hf.ae_pos] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (1 / f x))] with K hK
    have hKf : 1 ≤ (K : ℝ) * f x := (div_le_iff₀ hx).mp hK
    exact (max_eq_right (by linarith : 1 - (K : ℝ) * f x ≤ 0)).symm

/-- The low-rate assertion in (1174–1185), in quantified form. All choices
δ in the punctured interval share the same profile cutoff. -/
theorem ProfileLimit.lowRateDensity_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n : ℕ in atTop, lowRateDensity w n δ < ε := by
  obtain ⟨K, hK, hKpos⟩ := ((hf.lowTriangle_tail.eventually
    (gt_mem_nhds (show 0 < ε / 4 by positivity))).and (eventually_ge_atTop 1)).exists
  have hKr : 0 < (K : ℝ) := Nat.cast_pos.mpr (by omega)
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  intro δ _hδ hδK
  have he : Tendsto (fun n => 2 * (K : ℝ) *
      ∫ x, |stepProfile w n x - f x| ∂profileMeasure) atTop (𝓝 0) := by
    simpa using hf.tendsto_integral_abs_sub.const_mul (2 * (K : ℝ))
  filter_upwards [he.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity))] with n hn
  have hpoint (x : ℝ) :
      (if 0 < stepProfile w n x ∧ stepProfile w n x < δ then (1 : ℝ) else 0) ≤
        2 * K * |stepProfile w n x - f x| + 2 * max (1 - K * f x) 0 := by
    split_ifs with hx
    · have ha : 2 * (K : ℝ) * stepProfile w n x ≤ 1 := by
        have h := (le_div_iff₀ (show 0 < 2 * (K : ℝ) by positivity)).mp
          (hx.2.le.trans hδK)
        nlinarith
      have hmax := le_max_left (1 - (K : ℝ) * f x) 0
      have hmul := mul_le_mul_of_nonneg_left (le_abs_self (f x - stepProfile w n x)) hKr.le
      rw [abs_sub_comm (f x)] at hmul
      nlinarith
    · positivity
  have hErr : Integrable (fun x => 2 * (K : ℝ) * |stepProfile w n x - f x|)
      profileMeasure := ((integrable_stepProfile w n).sub hf.integrable).abs.const_mul _
  have hTail : Integrable (fun x => 2 * max (1 - (K : ℝ) * f x) 0) profileMeasure :=
    (((integrable_const 1).sub (hf.integrable.const_mul (K : ℝ))).sup
      (integrable_const 0)).const_mul _
  calc
    lowRateDensity w n δ = _ := lowRateDensity_eq_integral w n δ
    _ ≤ ∫ x, 2 * (K : ℝ) * |stepProfile w n x - f x| +
        2 * max (1 - (K : ℝ) * f x) 0 ∂profileMeasure :=
      integral_mono (integrable_lowProfile w n δ) (hErr.add hTail) hpoint
    _ = 2 * (K : ℝ) * (∫ x, |stepProfile w n x - f x| ∂profileMeasure) +
        2 * (∫ x, max (1 - (K : ℝ) * f x) 0 ∂profileMeasure) := by
      rw [integral_add hErr hTail, integral_const_mul, integral_const_mul]
    _ < ε := by linarith

end Luce
