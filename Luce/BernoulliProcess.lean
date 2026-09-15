import Luce.Predictable
import Luce.Stopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Adapted Bernoulli processes and their likelihoods

The probabilistic objects of Section 2. A predictable Bernoulli process is
specified by zero-one observations and their conditional probabilities.
The truncation preserves the conditional-expectation identity.
-/

open MeasureTheory Filter
open scoped BigOperators

namespace Luce

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)

/-- An adapted Bernoulli sequence and its predictable compensator atoms. -/
structure BernoulliProcess where
  filtration : Filtration ℕ mΩ
  observation : ℕ → Ω → ℝ
  probability : ℕ → Ω → ℝ
  adapted : ∀ k, StronglyMeasurable[filtration (k + 1)] (observation k)
  predictable : ∀ k, StronglyMeasurable[filtration k] (probability k)
  zero_one : ∀ k ω, observation k ω = 0 ∨ observation k ω = 1
  probability_nonneg : ∀ k ω, 0 ≤ probability k ω
  probability_le_one : ∀ k ω, probability k ω ≤ 1
  conditional_mean : ∀ k, μ[observation k | filtration k] =ᵐ[μ] probability k

namespace BernoulliProcess

variable {μ} [IsProbabilityMeasure μ] (X : BernoulliProcess μ)

lemma observation_nonneg (k : ℕ) (ω : Ω) : 0 ≤ X.observation k ω := by
  rcases X.zero_one k ω with h | h <;> rw [h] <;> norm_num

lemma observation_le_one (k : ℕ) (ω : Ω) : X.observation k ω ≤ 1 := by
  rcases X.zero_one k ω with h | h <;> rw [h] <;> norm_num

lemma integrable_observation (k : ℕ) : Integrable (X.observation k) μ :=
  ⟨((X.adapted k).mono (X.filtration.le (k + 1))).aestronglyMeasurable,
    HasFiniteIntegral.of_mem_Icc 0 1 (ae_of_all _ (fun ω =>
      ⟨X.observation_nonneg k ω, X.observation_le_one k ω⟩))⟩

lemma integrable_probability (k : ℕ) : Integrable (X.probability k) μ :=
  ⟨((X.predictable k).mono (X.filtration.le k)).aestronglyMeasurable,
    HasFiniteIntegral.of_mem_Icc 0 1 (ae_of_all _ (fun ω =>
      ⟨X.probability_nonneg k ω, X.probability_le_one k ω⟩))⟩

/-- Expected count equals expected compensator mass, without independence. -/
theorem integral_sum_observation (N : ℕ) :
    (∫ ω, ∑ k ∈ Finset.range N, X.observation k ω ∂μ) =
      ∫ ω, ∑ k ∈ Finset.range N, X.probability k ω ∂μ := by
  rw [integral_finset_sum _ (fun k _ => X.integrable_observation k),
    integral_finset_sum _ (fun k _ => X.integrable_probability k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [← integral_condExp (X.filtration.le k)]
  exact integral_congr_ae (X.conditional_mean k)

/-- Predictable deletion according to the two caps from the manuscript. -/
noncomputable def stop (δ K : ℝ) : BernoulliProcess μ where
  filtration := X.filtration
  observation k := {ω | keepTerm (fun j => X.probability j ω) δ K k}.indicator
    (X.observation k)
  probability k ω := stoppedProbability (fun j => X.probability j ω) δ K k
  adapted k := (X.adapted k).indicator
    (X.filtration.mono (Nat.le_succ k) _
      (measurableSet_keepTerm X.filtration X.probability
        (fun j => (X.predictable j).measurable) δ K k))
  predictable k := (measurable_stoppedProbability X.filtration X.probability
    (fun j => (X.predictable j).measurable) δ K k).stronglyMeasurable
  zero_one k ω := by
    by_cases h : keepTerm (fun j => X.probability j ω) δ K k
    · simpa [Set.indicator, h] using X.zero_one k ω
    · simp [Set.indicator, h]
  probability_nonneg k ω := stoppedProbability_nonneg (X.probability_nonneg k ω)
  probability_le_one k ω := (stoppedProbability_le (X.probability_nonneg k ω)).trans
    (X.probability_le_one k ω)
  conditional_mean k := by
    have hset := measurableSet_keepTerm X.filtration X.probability
      (fun j => (X.predictable j).measurable) δ K k
    have h := condExp_indicator (X.integrable_observation k) hset
    filter_upwards [h, X.conditional_mean k] with ω hc hm
    rw [hc]
    simp only [Set.indicator, Set.mem_setOf_eq, stoppedProbability]
    split_ifs <;> simp_all

lemma stop_probability_le_cap {δ K : ℝ} (hδ : 0 ≤ δ) (k : ℕ) (ω : Ω) :
    (X.stop δ K).probability k ω ≤ δ := stoppedProbability_le_cap _ hδ _

lemma stop_sum_probability_le_cap {δ K : ℝ} (hK : 0 ≤ K) (N : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range N, (X.stop δ K).probability k ω ≤ K := by
  change (∑ k ∈ Finset.range N,
    stoppedProbability (fun j => X.probability j ω) δ K k) ≤ K
  rw [sum_stoppedProbability]
  exact stoppedMass_le_cap _ hK _

/-- A factor of the likelihood martingale for a nonnegative test function. -/
noncomputable def laplaceFactor (g : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.exp (-g * X.observation k ω) /
    (1 - X.probability k ω * (1 - Real.exp (-g)))

lemma laplaceFactor_stronglyMeasurable (g : ℝ) (k : ℕ) :
    StronglyMeasurable[X.filtration (k + 1)] (X.laplaceFactor g k) := by
  have hnum := Real.continuous_exp.comp_stronglyMeasurable ((X.adapted k).const_mul (-g))
  have hp := (X.predictable k).mono (X.filtration.mono (Nat.le_succ k))
  exact hnum.mul (stronglyMeasurable_const.sub (hp.mul_const (1 - Real.exp (-g)))).inv₀

lemma laplaceFactor_bounds {δ g : ℝ} (hδ : δ < 1) (hg : 0 ≤ g) (k : ℕ) (ω : Ω)
    (hpδ : X.probability k ω ≤ δ) :
    0 ≤ X.laplaceFactor g k ω ∧ X.laplaceFactor g k ω ≤ 1 / (1 - δ) := by
  have hq : 0 ≤ 1 - Real.exp (-g) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hg))
  have hq1 : 1 - Real.exp (-g) ≤ 1 := by linarith [Real.exp_pos (-g)]
  have hden := likelihood_denominator_pos (X.probability_nonneg k ω) hpδ hδ hq1
  have hden' : 1 - δ ≤ 1 - X.probability k ω * (1 - Real.exp (-g)) := by
    have := mul_le_mul_of_nonneg_left hq1 (X.probability_nonneg k ω)
    linarith
  have hnum : Real.exp (-g * X.observation k ω) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg) (X.observation_nonneg k ω)
  exact ⟨div_nonneg (Real.exp_pos _).le hden.le,
    div_le_div₀ (by positivity) hnum (sub_pos.mpr hδ) hden'⟩

lemma laplaceFactor_integrable {δ g : ℝ} (hδ : δ < 1) (hg : 0 ≤ g) (k : ℕ)
    (hpδ : ∀ ω, X.probability k ω ≤ δ) : Integrable (X.laplaceFactor g k) μ :=
  ⟨((X.laplaceFactor_stronglyMeasurable g k).mono
      (X.filtration.le (k + 1))).aestronglyMeasurable,
    HasFiniteIntegral.of_mem_Icc 0 (1 / (1 - δ))
      (ae_of_all _ (fun ω => X.laplaceFactor_bounds hδ hg k ω (hpδ ω)))⟩

lemma laplaceFactor_conditional_mean {δ g : ℝ} (hδ : δ < 1) (hg : 0 ≤ g) (k : ℕ)
    (hpδ : ∀ ω, X.probability k ω ≤ δ) :
    μ[X.laplaceFactor g k | X.filtration k] =ᵐ[μ] (fun _ => 1) := by
  apply condExp_normalized_bernoulli (X.filtration.le k) (X.integrable_observation k)
    (X.conditional_mean k) (ae_of_all _ (X.zero_one k)) (X.predictable k) g
  · exact ae_of_all _ fun ω => (likelihood_denominator_pos (X.probability_nonneg k ω)
      (hpδ ω) hδ (by linarith [Real.exp_pos (-g)])).ne'
  · exact X.laplaceFactor_integrable hδ hg k hpδ

/-- Finite likelihood process. -/
noncomputable def likelihood (g : ℕ → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range N, X.laplaceFactor (g k) k ω

lemma likelihood_integrable {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) :
    Integrable (X.likelihood g N) μ := by
  have hm : StronglyMeasurable (X.likelihood g N) := by
    apply Finset.stronglyMeasurable_fun_prod
    intro k _
    exact (X.laplaceFactor_stronglyMeasurable (g k) k).mono (X.filtration.le (k + 1))
  refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_mem_Icc 0
    ((1 / (1 - δ)) ^ N) (ae_of_all _ (fun ω => ⟨?_, ?_⟩))⟩
  · exact Finset.prod_nonneg (fun k _ => (X.laplaceFactor_bounds hδ (hg k) k ω (hpδ k ω)).1)
  · calc
      X.likelihood g N ω ≤ ∏ _k ∈ Finset.range N, (1 / (1 - δ)) :=
        Finset.prod_le_prod (fun k _ => (X.laplaceFactor_bounds hδ (hg k) k ω (hpδ k ω)).1)
          (fun k _ => (X.laplaceFactor_bounds hδ (hg k) k ω (hpδ k ω)).2)
      _ = _ := by simp

theorem likelihood_martingale {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hpδ : ∀ k ω, X.probability k ω ≤ δ) :
    Martingale (X.likelihood g) X.filtration μ :=
  likelihood_product_martingale X.filtration (fun k => X.laplaceFactor (g k) k)
    (fun k => X.laplaceFactor_stronglyMeasurable (g k) k)
    (fun k => X.laplaceFactor_integrable hδ (hg k) k (hpδ k))
    (fun k => X.laplaceFactor_conditional_mean hδ (hg k) k (hpδ k))
    (X.likelihood_integrable hδ g hg hpδ)

theorem integral_likelihood {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) :
    (∫ ω, X.likelihood g N ω ∂μ) = 1 :=
  likelihood_product_integral X.filtration (fun k => X.laplaceFactor (g k) k)
    (fun k => X.laplaceFactor_stronglyMeasurable (g k) k)
    (fun k => X.laplaceFactor_integrable hδ (hg k) k (hpδ k))
    (fun k => X.laplaceFactor_conditional_mean hδ (hg k) k (hpδ k))
    (X.likelihood_integrable hδ g hg hpδ) N

/-- Product of conditional Laplace transforms. -/
noncomputable def laplaceProduct (g : ℕ → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range N, (1 - X.probability k ω * (1 - Real.exp (-g k)))

lemma likelihood_eq_laplace_div (g : ℕ → ℝ) (N : ℕ) (ω : Ω) :
    X.likelihood g N ω = Real.exp (-(∑ k ∈ Finset.range N, g k * X.observation k ω)) /
      X.laplaceProduct g N ω := by
  simp only [likelihood, laplaceFactor, laplaceProduct, Finset.prod_div_distrib,
    neg_mul, ← Real.exp_sum, Finset.sum_neg_distrib]

lemma laplaceProduct_bounds {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) (ω : Ω) :
    0 < X.laplaceProduct g N ω ∧ X.laplaceProduct g N ω ≤ 1 := by
  have hden k : 0 < 1 - X.probability k ω * (1 - Real.exp (-g k)) :=
    likelihood_denominator_pos (X.probability_nonneg k ω) (hpδ k ω) hδ
      (by linarith [Real.exp_pos (-g k)])
  refine ⟨Finset.prod_pos (fun k _ => hden k), Finset.prod_le_one
    (fun k _ => (hden k).le) (fun k _ => ?_)⟩
  have hq : 0 ≤ 1 - Real.exp (-g k) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg k)))
  linarith [mul_nonneg (X.probability_nonneg k ω) hq]

lemma laplaceProduct_integrable {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) : Integrable (X.laplaceProduct g N) μ := by
  have hm : StronglyMeasurable (X.laplaceProduct g N) := by
    apply Finset.stronglyMeasurable_fun_prod
    intro k _
    exact stronglyMeasurable_const.sub
      (((X.predictable k).mono (X.filtration.le k)).mul_const _)
  exact ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_mem_Icc 0 1 (ae_of_all _
    (fun ω => ⟨(X.laplaceProduct_bounds hδ g hg hpδ N ω).1.le,
      (X.laplaceProduct_bounds hδ g hg hpδ N ω).2⟩))⟩

lemma likelihood_mul_laplaceProduct {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) (ω : Ω) :
    X.likelihood g N ω * X.laplaceProduct g N ω =
      Real.exp (-(∑ k ∈ Finset.range N, g k * X.observation k ω)) := by
  rw [X.likelihood_eq_laplace_div]
  exact div_mul_cancel₀ _ (X.laplaceProduct_bounds hδ g hg hpδ N ω).1.ne'

/-- Uniform bound for the stopped likelihood from its total compensator cap. -/
lemma likelihood_bounds_of_sum_le {δ K : ℝ} (hδ : δ < 1) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) (ω : Ω)
    (hK : ∑ k ∈ Finset.range N, X.probability k ω ≤ K) :
    0 ≤ X.likelihood g N ω ∧ X.likelihood g N ω ≤ Real.exp (K / (1 - δ)) := by
  let x := fun k => X.probability k ω * (1 - Real.exp (-g k))
  have hx : ∀ k, 0 ≤ x k := fun k => mul_nonneg (X.probability_nonneg k ω)
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg k))))
  have hxp : ∀ k, x k ≤ X.probability k ω := fun k => by
    exact mul_le_of_le_one_right (X.probability_nonneg k ω)
      (by linarith [Real.exp_pos (-g k)])
  have hsum : ∑ k ∈ Finset.range N, x k ≤ K :=
    (Finset.sum_le_sum (fun k _ => hxp k)).trans hK
  have hinv := inverse_product_le_exp (Finset.range N) x (fun k _ => hx k)
    (fun k _ => (hxp k).trans (hpδ k ω)) hδ hsum
  have hp := (X.laplaceProduct_bounds hδ g hg hpδ N ω).1
  rw [X.likelihood_eq_laplace_div, div_eq_mul_inv]
  refine ⟨mul_nonneg (Real.exp_pos _).le (inv_pos.mpr hp).le, ?_⟩
  calc
    _ ≤ (X.laplaceProduct g N ω)⁻¹ := mul_le_of_le_one_left (inv_pos.mpr hp).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        (Finset.sum_nonneg (fun k _ => mul_nonneg (hg k) (X.observation_nonneg k ω)))))
    _ ≤ _ := hinv

end BernoulliProcess
end Luce
