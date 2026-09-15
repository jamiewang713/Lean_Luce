import Luce.Section5FiniteInsertion
import Luce.Section3Mean
import Luce.Section3Profile

/-!
# High-rate domination in Proposition 5.4

Source: `fixed_points.tex:1174–1206`. The finite half-mass assumption in the
density comparison is exposed and is later derived from the original profile
and normalization hypotheses. The windows are the paper's actual time windows.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal

namespace Luce
attribute [local instance] Classical.propDecidable

/-- The pointwise density comparison in (1191–1197), before integration. -/
theorem high_rate_density_bound {n : ℕ} (w : Weights n) (M : ℝ)
    (hmass : (n : ℝ) / 2 ≤ ∑ k ∈ Finset.univ.filter (fun k => w.rate k ≤ M), w.rate k)
    (i : Fin n) (hi : M < w.rate i) {t : ℝ} (ht : 0 ≤ t) :
    w.rate i * Real.exp (-(w.rate i * t)) ≤
      (2 * w.rate i / n) * ∑ k, w.rate k * Real.exp (-(w.rate k * t)) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hsum : ((n : ℝ) / 2) * Real.exp (-(w.rate i * t)) ≤
      ∑ k, w.rate k * Real.exp (-(w.rate k * t)) := by
    calc
      _ ≤ (∑ k ∈ Finset.univ.filter (fun k => w.rate k ≤ M), w.rate k) *
          Real.exp (-(w.rate i * t)) :=
        mul_le_mul_of_nonneg_right hmass (Real.exp_pos _).le
      _ = ∑ k ∈ Finset.univ.filter (fun k => w.rate k ≤ M),
          w.rate k * Real.exp (-(w.rate i * t)) := Finset.sum_mul _ _ _
      _ ≤ ∑ k ∈ Finset.univ.filter (fun k => w.rate k ≤ M),
          w.rate k * Real.exp (-(w.rate k * t)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (w.positive k).le
        apply Real.exp_le_exp.mpr
        have hkM := (Finset.mem_filter.mp hk).2
        nlinarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun k _ _ => mul_nonneg (w.positive k).le (Real.exp_pos _).le)
  have hc : 0 ≤ 2 * w.rate i / (n : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) (w.positive i).le) hn.le
  have hscale := mul_le_mul_of_nonneg_left hsum hc
  have heq : (2 * w.rate i / (n : ℝ)) * ((n : ℝ) / 2) = w.rate i := by
    field_simp
  simpa only [← mul_assoc, heq] using hscale

/-- Integrating the actual densities over J_j proves the column domination.
The zero extension at a tied background is handled explicitly. -/
theorem high_rate_ghostEntry_bound {n : ℕ} (w : Weights n) (ell : ℕ) (M : ℝ)
    (hmass : (n : ℝ) / 2 ≤ ∑ k ∈ Finset.univ.filter (fun k => w.rate k ≤ M), w.rate k)
    (old : Fin n → ℝ) (hnonneg : ∀ k, 0 ≤ old k)
    (i j : Fin n) (hi : M < w.rate i) :
    ghostEntry w ell old i j ≤ (2 * w.rate i / n) * ∑ k, ghostEntry w ell old k j := by
  by_cases hinj : Function.Injective old
  · have hInt (k : Fin n) := ghostEntry_eq_density_integral w ell old hinj hnonneg k j
    simp_rw [(hInt _).2]
    rw [← integral_finsetSum Finset.univ (fun k _ => (hInt k).1), ← integral_const_mul]
    apply integral_mono_ae (hInt i).1
      ((integrable_finsetSum _ (fun k _ => (hInt k).1)).const_mul _)
    filter_upwards [ae_restrict_mem (measurableSet_ghostWindowByOrder old hinj ell j)] with t ht
    exact high_rate_density_bound w M hmass i hi
      (ghostWindowByOrder_pos old hinj hnonneg ell j ht).le
  · simp [ghostEntry, ghostOrderKernel, hinj]

/-- High-rate mass, with the strict cutoff used in Proposition 5.4. -/
def highRateMass (w : WeightArray) (n : ℕ) (M : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => M < (w n).rate i), (w n).rate i) / n

lemma highRateMass_eq_integral (w : WeightArray) (n : ℕ) (M : ℝ) :
    highRateMass w n M =
      ∫ x, (if M < stepProfile w n x then stepProfile w n x else 0) ∂profileMeasure := by
  rw [integral_comp_stepProfile w n (fun a => if M < a then a else 0) (by simp)]
  simp [highRateMass, Finset.sum_filter]

lemma integrable_highProfile (w : WeightArray) (n : ℕ) (M : ℝ) :
    Integrable (fun x => if M < stepProfile w n x then stepProfile w n x else 0)
      profileMeasure := by
  apply (integrable_stepProfile w n).mono'
  · exact ((measurable_stepProfile w n).ite
      (measurableSet_lt measurable_const (measurable_stepProfile w n))
      measurable_const).aestronglyMeasurable
  · filter_upwards [] with x
    split_ifs
    · simp [Real.norm_eq_abs, abs_of_nonneg (stepProfile_nonneg w n x)]
    · simpa using stepProfile_nonneg w n x

/-- An integrable profile has a vanishing positive-part tail. Positivity is
not needed in this auxiliary analytic lemma. -/
lemma ProfileLimit.positivePart_tail {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) :
    Tendsto (fun K : ℕ => ∫ x, max (f x - K) 0 ∂profileMeasure) atTop (𝓝 0) := by
  have hm (K : ℕ) : AEStronglyMeasurable
      (fun x => max (f x - K) 0) profileMeasure :=
    ((hf.integrable.sub (integrable_const (K : ℝ))).sup
      (integrable_const 0)).aestronglyMeasurable
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun x => |f x|) hm hf.integrable.abs
  simp only [integral_zero] at h
  apply h
  · intro K
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self (f x), Nat.cast_nonneg (α := ℝ) K])
      (abs_nonneg _)
  · filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (f x))] with K hK
    exact (max_eq_right (sub_nonpos.mpr hK)).symm

/-- The high-rate assertion of (1174–1178), with both cutoffs and the order
of quantifiers explicit. No uniform-integrability hypothesis is assumed. -/
theorem ProfileLimit.highRateMass_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∀ᶠ n in atTop, highRateMass w n M < ε := by
  obtain ⟨K, hK⟩ := (hf.positivePart_tail.eventually
    (gt_mem_nhds (show 0 < ε / 4 by positivity))).exists
  refine ⟨2 * K + 1, by positivity, ?_⟩
  intro M hM
  filter_upwards [hf.tendsto_integral_abs_sub.eventually
    (gt_mem_nhds (show 0 < ε / 4 by positivity))] with n hn
  have hpoint (x : ℝ) :
      (if M < stepProfile w n x then stepProfile w n x else 0) ≤
        2 * |stepProfile w n x - f x| + 2 * max (f x - K) 0 := by
    split_ifs with hx
    · have h1 := le_abs_self (stepProfile w n x - f x)
      have h2 := le_max_left (f x - (K : ℝ)) 0
      linarith
    · positivity
  have hErr : Integrable (fun x => 2 * |stepProfile w n x - f x|) profileMeasure :=
    ((integrable_stepProfile w n).sub hf.integrable).abs.const_mul 2
  have hTail : Integrable (fun x => 2 * max (f x - K) 0) profileMeasure :=
    ((hf.integrable.sub (integrable_const (K : ℝ))).sup (integrable_const 0)).const_mul 2
  calc
    highRateMass w n M = _ := highRateMass_eq_integral w n M
    _ ≤ ∫ x, 2 * |stepProfile w n x - f x| + 2 * max (f x - K) 0
        ∂profileMeasure := integral_mono (integrable_highProfile w n M)
      (hErr.add hTail) hpoint
    _ = 2 * (∫ x, |stepProfile w n x - f x| ∂profileMeasure) +
        2 * (∫ x, max (f x - K) 0 ∂profileMeasure) := by
      rw [integral_add hErr hTail, integral_const_mul, integral_const_mul]
    _ < ε := by linarith

/-- The finite half-mass condition used above follows eventually from the
paper's assumptions. One cutoff threshold works for every larger M. -/
theorem ProfileLimit.eventually_moderate_half_mass {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / 2 ≤ ∑ k ∈ Finset.univ.filter (fun k => (w n).rate k ≤ M),
        (w n).rate k := by
  obtain ⟨M₀, hM₀, hM⟩ := hf.highRateMass_small (ε := 1 / 2) (by norm_num)
  refine ⟨M₀, hM₀, fun M hMM => ?_⟩
  filter_upwards [hM M hMM, eventually_ge_atTop 1] with n hn hnpos
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have htotal : ∑ k : Fin n, (w n).rate k = n := by
    have h := hnorm n (by omega)
    rw [one_div, mul_comm, ← div_eq_mul_inv, div_eq_iff hn'.ne'] at h
    simpa using h
  have hhigh : (∑ k ∈ Finset.univ.filter (fun k => M < (w n).rate k),
      (w n).rate k) < (n : ℝ) / 2 := by
    have h := (div_lt_iff₀ hn').mp hn
    linarith
  have hsplit :
      (∑ k ∈ Finset.univ.filter (fun k => (w n).rate k ≤ M), (w n).rate k) +
      (∑ k ∈ Finset.univ.filter (fun k => M < (w n).rate k), (w n).rate k) = n := by
    rw [← htotal, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : (w n).rate k ≤ M
    · simp [hk, not_lt.mpr hk]
    · simp [hk, lt_of_not_ge hk]
  linarith

end Luce
