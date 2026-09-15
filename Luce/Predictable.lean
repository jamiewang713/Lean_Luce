import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Predictable Bernoulli likelihoods

Finite-array ingredients of Lemma `lem:predictable-poisson` in Section 2 of
`fixed_points.tex`. The statements concern genuinely adapted indicators:
conditional expectations, rather than independence, give the martingale.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Luce

/-- The Laplace transform of a zero-one variable is affine in that variable. -/
theorem exp_neg_mul_of_zero_one {b g : ℝ} (hb : b = 0 ∨ b = 1) :
    Real.exp (-g * b) = 1 - (1 - Real.exp (-g)) * b := by
  rcases hb with rfl | rfl <;> simp

/-- The normalized Bernoulli likelihood has mean one. -/
theorem bernoulli_likelihood_mean {p q : ℝ} (hd : 1 - p * q ≠ 0) :
    (1 - p) * (1 / (1 - p * q)) + p * ((1 - q) / (1 - p * q)) = 1 := by
  field_simp
  ring

/-- The exact second moment used in the stopped likelihood estimate. -/
theorem bernoulli_likelihood_second_moment {p q : ℝ} (hd : 1 - p * q ≠ 0) :
    (1 - p) * (1 / (1 - p * q)) ^ 2 + p * ((1 - q) / (1 - p * q)) ^ 2 =
      1 + p * (1 - p) * q ^ 2 / (1 - p * q) ^ 2 := by
  field_simp
  ring

/-- Stopping at `p ≤ δ < 1` keeps every likelihood denominator positive. -/
theorem likelihood_denominator_pos {p q δ : ℝ} (hp : 0 ≤ p) (hpδ : p ≤ δ)
    (hδ : δ < 1) (hq : q ≤ 1) : 0 < 1 - p * q := by
  have := mul_le_mul_of_nonneg_left hq hp
  nlinarith

/-- A uniform exponential bound for the second moment of a stopped factor. -/
theorem bernoulli_likelihood_second_moment_le {p q δ : ℝ}
    (hp : 0 ≤ p) (hpδ : p ≤ δ) (hδ : δ < 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - p) * (1 / (1 - p * q)) ^ 2 + p * ((1 - q) / (1 - p * q)) ^ 2 ≤
      Real.exp (p / (1 - δ) ^ 2) := by
  have hd := likelihood_denominator_pos hp hpδ hδ hq1
  rw [bernoulli_likelihood_second_moment hd.ne']
  have hδ0 : 0 ≤ δ := hp.trans hpδ
  have hdδ : 0 < 1 - δ := sub_pos.mpr hδ
  have hp1 : p ≤ 1 := hpδ.trans hδ.le
  have hq2 : q ^ 2 ≤ 1 := by nlinarith
  have hn : p * (1 - p) * q ^ 2 ≤ p := by
    calc
      p * (1 - p) * q ^ 2 ≤ p * (1 - p) * 1 :=
        mul_le_mul_of_nonneg_left hq2 (mul_nonneg hp (sub_nonneg.mpr hp1))
      _ ≤ p := by nlinarith
  have hden : (1 - δ) ^ 2 ≤ (1 - p * q) ^ 2 := by
    have : p * q ≤ δ := (mul_le_mul_of_nonneg_left hq1 hp).trans (by simpa using hpδ)
    nlinarith
  have hfrac : p * (1 - p) * q ^ 2 / (1 - p * q) ^ 2 ≤ p / (1 - δ) ^ 2 :=
    div_le_div₀ (by positivity) hn (by positivity) hden
  have he := Real.add_one_le_exp (p / (1 - δ) ^ 2)
  linarith

section Conditional

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}

/-- Conditional Laplace transform identity for an adapted Bernoulli variable. -/
theorem condExp_bernoulli_laplace (hm : m ≤ mΩ) {I p : Ω → ℝ}
    (hI : Integrable I μ) (hIp : μ[I | m] =ᵐ[μ] p)
    (h01 : ∀ᵐ ω ∂μ, I ω = 0 ∨ I ω = 1) (g : ℝ) :
    μ[(fun ω => Real.exp (-g * I ω)) | m] =ᵐ[μ]
      (fun ω => 1 - (1 - Real.exp (-g)) * p ω) := by
  have heq : (fun ω => Real.exp (-g * I ω)) =ᵐ[μ]
      (fun ω => 1 - (1 - Real.exp (-g)) * I ω) :=
    h01.mono fun _ h => exp_neg_mul_of_zero_one h
  have hmul := condExp_smul (μ := μ) (1 - Real.exp (-g)) I m
  have hsub := condExp_sub (integrable_const (1 : ℝ))
    (hI.const_mul (1 - Real.exp (-g))) m
  refine (condExp_congr_ae heq).trans ?_
  filter_upwards [hsub, hmul, hIp] with ω hs hm' hp
  simp only [Pi.sub_def, Pi.smul_def, smul_eq_mul, condExp_const hm] at hs hm'
  rw [hs, hm', hp]

/-- Dividing the conditional Laplace transform by its predictable mean
produces a conditionally mean-one factor. -/
theorem condExp_normalized_bernoulli (hm : m ≤ mΩ) {I p : Ω → ℝ}
    (hI : Integrable I μ) (hIp : μ[I | m] =ᵐ[μ] p)
    (h01 : ∀ᵐ ω ∂μ, I ω = 0 ∨ I ω = 1) (hp : StronglyMeasurable[m] p)
    (g : ℝ) (hd : ∀ᵐ ω ∂μ, 1 - p ω * (1 - Real.exp (-g)) ≠ 0)
    (hint : Integrable (fun ω => Real.exp (-g * I ω) /
      (1 - p ω * (1 - Real.exp (-g)))) μ) :
    μ[(fun ω => Real.exp (-g * I ω) / (1 - p ω * (1 - Real.exp (-g)))) | m]
      =ᵐ[μ] (fun _ => 1) := by
  have hN : Integrable (fun ω => Real.exp (-g * I ω)) μ := by
    apply ((integrable_const (1 : ℝ)).sub (hI.const_mul (1 - Real.exp (-g)))).congr
    exact h01.mono (fun ω h => (exp_neg_mul_of_zero_one (g := g) h).symm)
  have hden : StronglyMeasurable[m] (fun ω => (1 - p ω * (1 - Real.exp (-g)))⁻¹) :=
    (stronglyMeasurable_const.sub (hp.mul_const _)).inv₀
  have hint' : Integrable ((fun ω => Real.exp (-g * I ω)) *
      (fun ω => (1 - p ω * (1 - Real.exp (-g)))⁻¹)) μ := by
    simpa only [Pi.mul_def, div_eq_mul_inv] using hint
  have h := condExp_mul_of_stronglyMeasurable_right hden hint' hN
  simp only [Pi.mul_def, ← div_eq_mul_inv] at h
  filter_upwards [h, condExp_bernoulli_laplace hm hI hIp h01 g, hd] with ω hc he hd'
  rw [hc, he]
  convert div_self hd' using 1 <;> ring

/-- Products of adapted, conditionally mean-one factors form a martingale.
Integrability is explicit; in the stopped construction it follows from the
positive lower bound on each denominator. -/
theorem likelihood_product_martingale (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k))
    (hYint : ∀ k, Integrable (Y k) μ)
    (hmean : ∀ k, μ[Y k | ℱ k] =ᵐ[μ] fun _ => 1)
    (hprod : ∀ k, Integrable (fun ω => ∏ j ∈ Finset.range k, Y j ω) μ) :
    Martingale (fun k ω => ∏ j ∈ Finset.range k, Y j ω) ℱ μ := by
  have hadapt : StronglyAdapted ℱ (fun k ω => ∏ j ∈ Finset.range k, Y j ω) := by
    intro k
    exact (Finset.range k).stronglyMeasurable_fun_prod (fun j hj =>
      (hY j).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hj))))
  apply martingale_nat hadapt hprod
  intro k
  have hstep : (fun ω => ∏ j ∈ Finset.range (k + 1), Y j ω) =
      (fun ω => ∏ j ∈ Finset.range k, Y j ω) * Y k := by
    funext ω
    simp [Finset.prod_range_succ]
  have hcond := condExp_mul_of_stronglyMeasurable_left (hadapt k)
    (hstep ▸ hprod (k + 1)) (hYint k)
  rw [hstep]
  filter_upwards [hcond, hmean k] with ω hc hm
  simp only [Pi.mul_apply] at hc
  rw [hc, hm, mul_one]

/-- Every finite likelihood product has expectation one. -/
theorem likelihood_product_integral (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k))
    (hYint : ∀ k, Integrable (Y k) μ)
    (hmean : ∀ k, μ[Y k | ℱ k] =ᵐ[μ] fun _ => 1)
    (hprod : ∀ k, Integrable (fun ω => ∏ j ∈ Finset.range k, Y j ω) μ) (k : ℕ) :
    (∫ ω, ∏ j ∈ Finset.range k, Y j ω ∂μ) = 1 := by
  have h := likelihood_product_martingale ℱ Y hY hYint hmean hprod
  have hc := h.condExp_ae_eq (Nat.zero_le k)
  have hi := integral_congr_ae hc
  rw [integral_condExp (ℱ.le 0)] at hi
  simpa using hi

/-- A bounded mean-one likelihood transfers an `L¹` approximation to its
weighted expectation. This justifies the expectation passage in Section 2. -/
theorem likelihood_integral_error {L A : Ω → ℝ} {C c : ℝ}
    (hL : Integrable L μ) (hA : Integrable A μ)
    (hmean : (∫ ω, L ω ∂μ) = 1)
    (hL0 : ∀ᵐ ω ∂μ, 0 ≤ L ω) (hLC : ∀ᵐ ω ∂μ, L ω ≤ C) :
    |(∫ ω, L ω * A ω ∂μ) - c| ≤ C * ∫ ω, |A ω - c| ∂μ := by
  have hbound : ∀ᵐ ω ∂μ, ‖L ω‖ ≤ C := by
    filter_upwards [hL0, hLC] with ω h0 hC
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using hC
  have hdiff : Integrable (fun ω => A ω - c) μ := hA.sub (integrable_const c)
  have hLA := hA.bdd_mul hL.aestronglyMeasurable hbound
  have hLD := hdiff.bdd_mul hL.aestronglyMeasurable hbound
  have heq : (∫ ω, L ω * A ω ∂μ) - c = ∫ ω, L ω * (A ω - c) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub hLA (hL.mul_const c), integral_mul_const, hmean, one_mul]
  rw [heq]
  calc
    |∫ ω, L ω * (A ω - c) ∂μ| ≤ ∫ ω, |L ω * (A ω - c)| ∂μ :=
      by simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := μ) (fun ω => L ω * (A ω - c))
    _ ≤ ∫ ω, C * |A ω - c| ∂μ := by
      apply integral_mono_ae hLD.abs (hdiff.abs.const_mul C)
      filter_upwards [hL0, hLC] with ω h0 hC
      rw [abs_mul, abs_of_nonneg h0]
      exact mul_le_mul_of_nonneg_right hC (abs_nonneg _)
    _ = _ := integral_const_mul _ _

end Conditional

/-- Explicit quadratic remainder in the logarithm expansion. -/
theorem log_one_sub_remainder {x δ : ℝ} (hx : 0 ≤ x) (hxδ : x ≤ δ)
    (hδ : δ < 1) : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - δ) := by
  have hx1 : |x| < 1 := by
    rw [abs_of_nonneg hx]
    exact hxδ.trans_lt hδ
  have h : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_of_nonneg hx, add_comm] using Real.abs_log_sub_add_sum_range_le hx1 1
  exact h.trans (div_le_div_of_nonneg_left (sq_nonneg x) (sub_pos.mpr hδ)
    (by linarith))

/-- The logarithmic product error is controlled by the largest atom times
the total compensator. This is the deterministic expansion in Section 2. -/
theorem log_product_remainder {ι : Type*} (s : Finset ι) (x : ι → ℝ) {δ : ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (hxδ : ∀ i ∈ s, x i ≤ δ) (hδ : δ < 1) :
    |Real.log (∏ i ∈ s, (1 - x i)) + ∑ i ∈ s, x i| ≤
      δ * (∑ i ∈ s, x i) / (1 - δ) := by
  rw [Real.log_prod (fun i hi => (sub_pos.mpr ((hxδ i hi).trans_lt hδ)).ne'),
    ← Finset.sum_add_distrib]
  calc
    |∑ i ∈ s, (Real.log (1 - x i) + x i)| ≤
        ∑ i ∈ s, |Real.log (1 - x i) + x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, x i ^ 2 / (1 - δ) :=
      Finset.sum_le_sum (fun i hi => log_one_sub_remainder (hx i hi) (hxδ i hi) hδ)
    _ ≤ ∑ i ∈ s, δ * x i / (1 - δ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ (sub_pos.mpr hδ).le
      nlinarith [hx i hi, hxδ i hi]
    _ = δ * (∑ i ∈ s, x i) / (1 - δ) := by
      rw [← Finset.sum_div, ← Finset.mul_sum]

/-- Exponentiation on the negative half-line is one-Lipschitz. -/
theorem exp_sub_le_sub_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · simpa only [abs_sub_comm] using this hb ha (le_of_not_ge hab)
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hab)),
    abs_of_nonpos (sub_nonpos.mpr hab)]
  have he := Real.one_sub_le_exp_neg (b - a)
  have he' := mul_le_mul_of_nonneg_left he (Real.exp_pos b).le
  have heq : Real.exp b * Real.exp (-(b - a)) = Real.exp a := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at he'
  have hexp : Real.exp b ≤ 1 := Real.exp_le_one_iff.mpr hb
  have hmul := mul_le_mul_of_nonneg_right hexp (sub_nonneg.mpr hab)
  nlinarith

/-- Quantitative Poisson-product approximation for a finite array. -/
theorem product_poisson_error {ι : Type*} (s : Finset ι) (x : ι → ℝ) {δ lam : ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (hxδ : ∀ i ∈ s, x i ≤ δ)
    (hδ : δ < 1) (hlam : 0 ≤ lam) :
    |(∏ i ∈ s, (1 - x i)) - Real.exp (-lam)| ≤
      δ * (∑ i ∈ s, x i) / (1 - δ) + |(∑ i ∈ s, x i) - lam| := by
  have hprod : 0 < ∏ i ∈ s, (1 - x i) :=
    Finset.prod_pos fun i hi => sub_pos.mpr ((hxδ i hi).trans_lt hδ)
  have hprod1 : (∏ i ∈ s, (1 - x i)) ≤ 1 :=
    Finset.prod_le_one (fun i hi => (sub_pos.mpr ((hxδ i hi).trans_lt hδ)).le)
      (fun i hi => by linarith [hx i hi])
  have hlog : Real.log (∏ i ∈ s, (1 - x i)) ≤ 0 :=
    Real.log_nonpos hprod.le hprod1
  have hsum : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx
  calc
    |(∏ i ∈ s, (1 - x i)) - Real.exp (-lam)| ≤
        |(∏ i ∈ s, (1 - x i)) - Real.exp (-(∑ i ∈ s, x i))| +
          |Real.exp (-(∑ i ∈ s, x i)) - Real.exp (-lam)| := abs_sub_le _ _ _
    _ ≤ |Real.log (∏ i ∈ s, (1 - x i)) + ∑ i ∈ s, x i| +
          |(∑ i ∈ s, x i) - lam| := by
      apply add_le_add
      · simpa only [Real.exp_log hprod, sub_neg_eq_add] using
          exp_sub_le_sub_of_nonpos hlog (neg_nonpos.mpr hsum)
      · simpa only [neg_sub_neg, abs_sub_comm] using
          exp_sub_le_sub_of_nonpos (neg_nonpos.mpr hsum) (neg_nonpos.mpr hlam)
    _ ≤ _ := add_le_add (log_product_remainder s x hx hxδ hδ) le_rfl

/-- A deterministic bound for the stopped likelihood, avoiding any independence
assumption and giving uniform integrability directly. -/
theorem inverse_product_le_exp {ι : Type*} (s : Finset ι) (x : ι → ℝ) {δ K : ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (hxδ : ∀ i ∈ s, x i ≤ δ)
    (hδ : δ < 1) (hsum : ∑ i ∈ s, x i ≤ K) :
    (∏ i ∈ s, (1 - x i))⁻¹ ≤ Real.exp (K / (1 - δ)) := by
  have hprod : 0 < ∏ i ∈ s, (1 - x i) :=
    Finset.prod_pos fun i hi => sub_pos.mpr ((hxδ i hi).trans_lt hδ)
  have herr := (abs_le.mp (log_product_remainder s x hx hxδ hδ)).1
  have hlog : -Real.log (∏ i ∈ s, (1 - x i)) ≤ K / (1 - δ) := by
    have hsum' := (div_le_div_of_nonneg_right hsum (sub_pos.mpr hδ).le)
    have hid : (∑ i ∈ s, x i) + δ * (∑ i ∈ s, x i) / (1 - δ) =
        (∑ i ∈ s, x i) / (1 - δ) := by
      field_simp [(sub_pos.mpr hδ).ne']
      ring
    linarith
  simpa only [Real.exp_neg, Real.exp_log hprod] using Real.exp_le_exp.mpr hlog

/-- A form of the product error separating a fixed denominator cap from a
possibly random upper bound on the largest atom. -/
theorem product_poisson_error_of_atom_bound {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {a δ K lam : ℝ} (hx : ∀ i ∈ s, 0 ≤ x i) (hxa : ∀ i ∈ s, x i ≤ a)
    (ha : 0 ≤ a) (haδ : a ≤ δ) (hδ : δ < 1)
    (hsum : ∑ i ∈ s, x i ≤ K) (hlam : 0 ≤ lam) :
    |(∏ i ∈ s, (1 - x i)) - Real.exp (-lam)| ≤
      K / (1 - δ) * a + |(∑ i ∈ s, x i) - lam| := by
  have hsum0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx
  have hK : 0 ≤ K := hsum0.trans hsum
  apply (product_poisson_error s x hx hxa (haδ.trans_lt hδ) hlam).trans
  apply add_le_add _ le_rfl
  calc
    a * (∑ i ∈ s, x i) / (1 - a) ≤ a * K / (1 - a) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum ha)
        (sub_pos.mpr (haδ.trans_lt hδ)).le
    _ ≤ a * K / (1 - δ) := div_le_div_of_nonneg_left (mul_nonneg ha hK)
      (sub_pos.mpr hδ) (by linarith)
    _ = K / (1 - δ) * a := by ring

end Luce
