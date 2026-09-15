import Luce.Section6BernoulliCharacteristicDrift
import Luce.Section6BernoulliGaussianScale
import Luce.Section6ComplexProbabilityConvergence

/-! Characteristic-function convergence under a deterministic compensator cap. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace Luce.BernoulliCLT

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
  (X : ∀ n, BernoulliProcess (μ n)) (N : ℕ → ℕ) {v : ℕ → ℝ}

theorem scaled_coefficient_bounds {v t : ℝ} (hv : 0 < v) :
    -(coefficient (t/Real.sqrt v)).re * (2*v) ≤ 4*t^2 ∧
    ‖coefficient (t/Real.sqrt v)‖^2 * v ≤ 16*t^2 := by
  have hs := Real.sqrt_pos.mpr hv
  have he : (t/Real.sqrt v)^2 * v = t^2 := by
    rw [div_pow, Real.sq_sqrt hv.le]
    field_simp
  constructor
  · have h := mul_le_mul_of_nonneg_right (coefficient_neg_re_le_all (t/Real.sqrt v))
      (by positivity : 0 ≤ 2*v)
    nlinarith [he]
  · have h := coefficient_norm_le_all (t/Real.sqrt v)
    have h2 : ‖coefficient (t/Real.sqrt v)‖^2 ≤ 16*(t/Real.sqrt v)^2 := by
      nlinarith [sq_abs (t/Real.sqrt v), norm_nonneg (coefficient (t/Real.sqrt v)),
        abs_nonneg (t/Real.sqrt v)]
    nlinarith [mul_le_mul_of_nonneg_right h2 hv.le]

theorem capped_compensation_tendsto (hv : ∀ n, 1 ≤ v n) (hvlim : Tendsto v atTop atTop)
    (hcap : ∀ n ω, (X n).cltMass (N n) ω ≤ 2*v n)
    (hB : ConvergesInProbability μ (fun n ω => (X n).cltSquares (N n) ω/v n) 0)
    (t : ℝ) :
    Tendsto (fun n => ∫ ω, (X n).characteristicCompensation
      (t/Real.sqrt (v n)) (N n) ω ∂μ n) atTop (𝓝 1) := by
  have hv0 (n : ℕ) : 0 < v n := lt_of_lt_of_le zero_lt_one (hv n)
  have hb := hB.integral_abs_tendsto
    (fun n => ((X n).cltSquares_measurable (N n)).div_const _)
    (B := 2) (fun n ω => by
      rw [sub_zero, abs_of_nonneg (div_nonneg ((X n).cltSquares_nonneg _ _) (hv0 n).le)]
      exact (div_le_iff₀ (hv0 n)).mpr ((X n).cltSquares_le_mass _ _ |>.trans (hcap n ω)))
  simp only [sub_zero, abs_of_nonneg (div_nonneg (BernoulliProcess.cltSquares_nonneg _ _ _)
    (hv0 _).le)] at hb
  have hu : Tendsto (fun n => t/Real.sqrt (v n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hvlim)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    _ (by simpa using hb.const_mul (Real.exp (4*t^2)*(48*t^2)))
  filter_upwards [(hu.abs).eventually (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1/4))]
    with n hn
  have ha : ‖coefficient (t/Real.sqrt (v n))‖ ≤ 1 :=
    (coefficient_norm_le_all _).trans (by linarith)
  have h := (X n).characteristicCompensation_error ha (hcap n)
  have hbnd := scaled_coefficient_bounds (t := t) (hv0 n)
  have hsq : ‖coefficient (t/Real.sqrt (v n))‖^2 ≤ 16*t^2/v n :=
    (le_div_iff₀ (hv0 n)).mpr hbnd.2
  apply h.trans
  rw [integral_div]
  have hI : 0 ≤ ∫ ω, (X n).cltSquares (N n) ω ∂μ n :=
    integral_nonneg fun ω => (X n).cltSquares_nonneg _ _
  calc
    _ ≤ (Real.exp (4*t^2)*(3*(16*t^2/v n))) *
        (∫ ω, (X n).cltSquares (N n) ω ∂μ n) := by
      apply mul_le_mul_of_nonneg_right _ hI
      exact mul_le_mul (Real.exp_le_exp.mpr hbnd.1)
        (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity) (by positivity)
    _ = _ := by ring

theorem capped_characteristic_tendsto (hv : ∀ n, 1 ≤ v n) (hvlim : Tendsto v atTop atTop)
    (hcap : ∀ n ω, (X n).cltMass (N n) ω ≤ 2*v n)
    (hA : ConvergesInProbability μ
      (fun n ω => ((X n).cltMass (N n) ω-v n)/Real.sqrt (v n)) 0)
    (hB : ConvergesInProbability μ (fun n ω => (X n).cltSquares (N n) ω/v n) 0)
    (t : ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp
      (((((X n).cltCount (N n) ω-v n)/Real.sqrt (v n))*t : ℝ) * Complex.I) ∂μ n)
      atTop (𝓝 (Complex.exp (-(t : ℂ)^2/2))) := by
  let u (n : ℕ) := t/Real.sqrt (v n)
  let a (n : ℕ) := coefficient (u n)
  let Z (n : ℕ) := (X n).characteristicCompensation (u n) (N n)
  let f (n : ℕ) (ω : Ω n) : ℂ :=
    a n * (X n).cltMass (N n) ω - (u n : ℂ)*Complex.I*v n
  let g (n : ℕ) : ℂ := a n*v n - (u n : ℂ)*Complex.I*v n
  have hv0 (n : ℕ) : 0 < v n := lt_of_lt_of_le zero_lt_one (hv n)
  have hZ (n : ℕ) : Integrable (Z n) (μ n) :=
    (X n).characteristicCompensation_integrable _ _
  have hZbound (n : ℕ) (ω : Ω n) : ‖Z n ω‖ ≤ Real.exp (4*t^2) :=
    ((X n).characteristicCompensation_bound (u n) (hcap n) le_rfl ω).trans
      (Real.exp_le_exp.mpr (scaled_coefficient_bounds (t := t) (hv0 n)).1)
  have hf (n : ℕ) : Measurable (f n) :=
    ((Complex.measurable_ofReal.comp ((X n).cltMass_measurable (N n))).const_mul _).sub_const _
  have hfre (n : ℕ) (ω : Ω n) : (f n ω).re ≤ 0 := by
    simp only [f, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      mul_one, zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (coefficient_re_nonpos _) ((X n).cltMass_nonneg _ _)
  have hgre (n : ℕ) : (g n).re ≤ 0 := by
    simp only [g, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      mul_one, zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (coefficient_re_nonpos _) (hv0 n).le
  have hF (n : ℕ) : Integrable (fun ω => Complex.exp (f n ω)) (μ n) :=
    (integrable_const (1 : ℝ)).mono' (Complex.measurable_exp.comp (hf n)).aestronglyMeasurable
      (ae_of_all _ fun ω => norm_exp_le_one (hfre n ω))
  have hdiff := integral_exp_difference_tendsto μ hf (fun _ => measurable_const)
    hfre (fun n _ => hgre n) (C := 1+4*|t|) (by positivity) (R := fun n ω =>
      ((X n).cltMass (N n) ω-v n)/Real.sqrt (v n)) (g := fun n _ => g n)
      (by
        intro n ω
        have hs := Real.sqrt_pos.mpr (hv0 n)
        have he : f n ω-g n = a n*((X n).cltMass (N n) ω-v n) := by dsimp [f,g]; ring
        rw [he, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        calc
          _ ≤ (4 * |u n|) * |(X n).cltMass (N n) ω-v n| :=
            mul_le_mul_of_nonneg_right (coefficient_norm_le_all _) (abs_nonneg _)
          _ = 4 * |t| * |((X n).cltMass (N n) ω-v n)/Real.sqrt (v n)| := by
            simp only [u, abs_div, abs_of_pos hs]
            ring
          _ ≤ _ := by nlinarith [abs_nonneg (((X n).cltMass (N n) ω-v n)/Real.sqrt (v n))]) hA
  have heZ := capped_compensation_tendsto μ X N hv hvlim hcap hB t
  have heG := gaussian_factor_tendsto hvlim t
  have hprod : Tendsto (fun n => Complex.exp (g n)*(∫ ω, Z n ω ∂μ n))
      atTop (𝓝 (Complex.exp (-(t : ℂ)^2/2))) := by
    simpa only [mul_one] using heG.mul heZ
  have herr : Tendsto (fun n =>
      (∫ ω, Z n ω*Complex.exp (f n ω) ∂μ n) -
        Complex.exp (g n)*(∫ ω, Z n ω ∂μ n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _
      (by simpa using hdiff.const_mul (Real.exp (4*t^2)))
    intro n
    exact integral_complex_product_error (hZ n) (hF n) (hZbound n)
  have hlim := herr.add hprod
  simp only [sub_add_cancel, zero_add] at hlim
  convert hlim using 1
  ext n
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  dsimp [Z, BernoulliProcess.characteristicCompensation, f, g, a]
  rw [← Complex.exp_add]
  congr 1
  dsimp [u]
  push_cast
  ring

end Luce.BernoulliCLT
