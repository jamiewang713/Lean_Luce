import Luce.Profile
import Mathlib.Probability.Moments.Variance

/-!
# Estimates for the interior race

Finite-grid interpolation, weighted variance, and denominator replacement
estimates from Section 3 of `fixed_points.tex`.  The probability bounds here
use genuine independence and variance; the estimates are stated separately
from the still-to-be-assembled full interior compensator theorem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- Monotonicity turns two grid-point bounds and two bounds on the limiting
function's oscillation into a bound at every intervening point. -/
theorem monotone_bracket_error {f g : ℝ → ℝ} (hg : Monotone g)
    {a t b ε δ : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (ha : |g a - f a| ≤ ε) (hb : |g b - f b| ≤ ε)
    (hfa : |f t - f a| ≤ δ) (hfb : |f b - f t| ≤ δ) :
    |g t - f t| ≤ ε + δ := by
  have hga := hg hat
  have hgb := hg htb
  rw [abs_le] at ha hb hfa hfb ⊢
  constructor <;> linarith

/-- The finite-grid upgrade used for the empirical arrival distribution. -/
theorem monotone_grid_error {f g : ℝ → ℝ} (hg : Monotone g)
    (grid : Finset ℝ) (domain : Set ℝ) {ε δ : ℝ}
    (hgrid : ∀ t ∈ grid, |g t - f t| ≤ ε)
    (hcover : ∀ t ∈ domain, ∃ a ∈ grid, ∃ b ∈ grid,
      a ≤ t ∧ t ≤ b ∧ |f t - f a| ≤ δ ∧ |f b - f t| ≤ δ) :
    ∀ t ∈ domain, |g t - f t| ≤ ε + δ := by
  intro t ht
  obtain ⟨a, ha, b, hb, hat, htb, hfa, hfb⟩ := hcover t ht
  exact monotone_bracket_error hg hat htb (hgrid a ha) (hgrid b hb) hfa hfb

/-- The same grid argument for decreasing remaining-rate functions. -/
theorem antitone_bracket_error {f g : ℝ → ℝ} (hg : Antitone g)
    {a t b ε δ : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (ha : |g a - f a| ≤ ε) (hb : |g b - f b| ≤ ε)
    (hfa : |f t - f a| ≤ δ) (hfb : |f b - f t| ≤ δ) :
    |g t - f t| ≤ ε + δ := by
  have hga := hg hat
  have hgb := hg htb
  rw [abs_le] at ha hb hfa hfb ⊢
  constructor <;> linarith

/-- The weight sum of squares is controlled by the largest weight times
the total weight. -/
theorem sum_sq_le_max_mul_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) {M : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hM : ∀ i ∈ s, w i ≤ M) :
    ∑ i ∈ s, (w i)^2 ≤ M * ∑ i ∈ s, w i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  nlinarith [mul_le_mul_of_nonneg_right (hM i hi) (hw i hi)]

/-- The deterministic estimate behind the remaining-rate variance bound. -/
theorem normalized_sum_sq_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) {M N : ℝ}
    (hN : 0 < N) (hw : ∀ i ∈ s, 0 ≤ w i) (hM : ∀ i ∈ s, w i ≤ M)
    (hsum : ∑ i ∈ s, w i = N) :
    (∑ i ∈ s, (w i)^2) / N^2 ≤ M / N := by
  have h := sum_sq_le_max_mul_sum s w hw hM
  rw [hsum] at h
  apply (div_le_div_iff₀ (sq_pos_of_pos hN) hN).mpr
  nlinarith [mul_le_mul_of_nonneg_right h hN.le]

section Variance

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Independent variables with the weight-square variance bounds satisfy
the precise normalized variance estimate used in the race law. -/
theorem variance_normalized_sum_le (s : Finset ι) (X : ι → Ω → ℝ)
    (w : ι → ℝ) {M N : ℝ} (hN : 0 < N)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hM : ∀ i ∈ s, w i ≤ M)
    (hsum : ∑ i ∈ s, w i = N)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hind : Set.Pairwise ↑s fun i j => IndepFun (X i) (X j) μ)
    (hvar : ∀ i ∈ s, variance (X i) μ ≤ (w i)^2) :
    variance (fun ω => (∑ i ∈ s, X i ω) / N) μ ≤ M / N := by
  have hsumvar := IndepFun.variance_sum hX hind
  have heq : (fun ω => (∑ i ∈ s, X i ω) / N) =
      fun ω => N⁻¹ * (∑ i ∈ s, X i) ω := by
    funext ω
    simp [div_eq_mul_inv, mul_comm]
  rw [heq, variance_const_mul, hsumvar]
  calc
    N⁻¹ ^ 2 * ∑ i ∈ s, variance (X i) μ
      ≤ N⁻¹ ^ 2 * ∑ i ∈ s, (w i)^2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hvar) (sq_nonneg _)
    _ = (∑ i ∈ s, (w i)^2) / N^2 := by ring
    _ ≤ M / N := normalized_sum_sq_le s w hN hw hM hsum

end Variance

/-- A positive deterministic denominator remains bounded away from zero
when the empirical denominator is sufficiently close. -/
theorem denominator_lower_bound {D W d : ℝ} (hdD : d ≤ D)
    (herror : |W - D| ≤ d / 2) : d / 2 ≤ W := by
  have := (abs_le.mp herror).1
  linarith

/-- The maximum predictable probability estimate on the good race event. -/
theorem probability_le_of_denominator_close {w D W d : ℝ}
    (hw : 0 ≤ w) (hd : 0 < d) (hdD : d ≤ D) (herror : |W - D| ≤ d / 2) :
    w / W ≤ 2 * w / d := by
  have hW := denominator_lower_bound hdD herror
  have hWpos : 0 < W := lt_of_lt_of_le (half_pos hd) hW
  apply (div_le_div_iff₀ hWpos hd).mpr
  nlinarith [mul_le_mul_of_nonneg_left hW hw]

/-- Quantitative denominator replacement in the interior compensator. -/
theorem abs_div_sub_div_le {w D W d ε : ℝ} (hw : 0 ≤ w) (hd : 0 < d)
    (hdD : d ≤ D) (hdW : d ≤ W) (herror : |W - D| ≤ ε) :
    |w / W - w / D| ≤ w * ε / d^2 := by
  have hD : 0 < D := hd.trans_le hdD
  have hW : 0 < W := hd.trans_le hdW
  have hε : 0 ≤ ε := (abs_nonneg _).trans herror
  have heq : w / W - w / D = w * (D - W) / (W * D) := by field_simp
  rw [heq, abs_div, abs_mul, abs_of_nonneg hw, abs_sub_comm,
    abs_of_pos (mul_pos hW hD)]
  apply (div_le_div_iff₀ (mul_pos hW hD) (sq_pos_of_pos hd)).mpr
  have hprod : d^2 ≤ W * D := by nlinarith [mul_le_mul hdW hdD hd.le hW.le]
  calc
    w * |W - D| * d^2 ≤ w * ε * d^2 := by gcongr
    _ ≤ w * ε * (W * D) := by gcongr

/-- Evaluation at perturbed times splits into the uniform race error and
the deterministic continuity error. -/
theorem random_time_substitution_bound {D Dhat : ℝ → ℝ}
    {t τ ε δ : ℝ} (hrace : |Dhat τ - D τ| ≤ ε) (htime : |D τ - D t| ≤ δ) :
    |Dhat τ - D t| ≤ ε + δ := by
  calc
    |Dhat τ - D t| ≤ |Dhat τ - D τ| + |D τ - D t| := abs_sub_le _ _ _
    _ ≤ ε + δ := add_le_add hrace htime

end Luce
