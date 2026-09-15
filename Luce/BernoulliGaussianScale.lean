import Luce.BernoulliCharacteristicEstimates

/-! Deterministic scaling and the Gaussian characteristic-function limit. -/

noncomputable section
open Filter
open scoped Topology

namespace Luce.BernoulliCLT

theorem gaussian_exponent_error {v t : ℝ} (hv : 0 < v)
    (hu : |t / Real.sqrt v| ≤ 1) :
    ‖coefficient (t / Real.sqrt v) * v -
      ((t / Real.sqrt v : ℝ) : ℂ) * Complex.I * v + (t : ℂ)^2 / 2‖ ≤
      |t|^3 / Real.sqrt v := by
  let u := t / Real.sqrt v
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hs2 := Real.sq_sqrt hv.le
  have hu2 : u^2 * v = t^2 := by dsimp [u]; field_simp; nlinarith [hs2]
  have hc2 : (u : ℂ)^2 * (v : ℂ) = (t : ℂ)^2 := by exact_mod_cast hu2
  have ht := Complex.exp_bound (x := (u : ℂ) * Complex.I)
    (by simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one] using hu) (n := 3) (by decide)
  have he : Complex.exp ((u : ℂ) * Complex.I) -
      ∑ m ∈ Finset.range 3, ((u : ℂ) * Complex.I)^m / m.factorial =
      coefficient u - (u : ℂ) * Complex.I + (u : ℂ)^2/2 := by
    simp [Finset.sum_range_succ, coefficient, mul_pow, Complex.I_sq]
    ring
  rw [he] at ht
  have hb : ‖coefficient u - (u : ℂ) * Complex.I + (u : ℂ)^2/2‖ ≤ |u|^3 := by
    apply ht.trans
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    norm_num
    nlinarith [abs_nonneg u, pow_nonneg (abs_nonneg u) 3]
  have he2 : coefficient u * v - (u : ℂ) * Complex.I * v + (t : ℂ)^2/2 =
      (coefficient u - (u : ℂ) * Complex.I + (u : ℂ)^2/2) * v := by
    rw [← hc2]
    ring
  change ‖coefficient u * v - (u : ℂ) * Complex.I * v + (t : ℂ)^2/2‖ ≤ _
  rw [he2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
  calc
    _ ≤ |u|^3 * v := mul_le_mul_of_nonneg_right hb hv.le
    _ = |t|^3 / Real.sqrt v := by
      dsimp [u]
      rw [abs_div, abs_of_pos hs]
      field_simp
      rw [hs2]

theorem gaussian_exponent_tendsto {v : ℕ → ℝ} (hv : Tendsto v atTop atTop) (t : ℝ) :
    Tendsto (fun n => coefficient (t / Real.sqrt (v n)) * (v n : ℂ) -
      ((t / Real.sqrt (v n) : ℝ) : ℂ) * Complex.I * (v n : ℂ))
      atTop (𝓝 (-(t : ℂ)^2/2)) := by
  have hs := Real.tendsto_sqrt_atTop.comp hv
  have hu : Tendsto (fun n => t / Real.sqrt (v n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have herr : Tendsto (fun n => |t|^3 / Real.sqrt (v n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ herr
  filter_upwards [hv.eventually_gt_atTop 0, (hu.abs).eventually (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))]
    with n hn hu'
  simpa only [sub_neg_eq_add, neg_div] using gaussian_exponent_error hn hu'.le

theorem gaussian_factor_tendsto {v : ℕ → ℝ} (hv : Tendsto v atTop atTop) (t : ℝ) :
    Tendsto (fun n => Complex.exp (coefficient (t / Real.sqrt (v n)) * (v n : ℂ) -
      ((t / Real.sqrt (v n) : ℝ) : ℂ) * Complex.I * (v n : ℂ)))
      atTop (𝓝 (Complex.exp (-(t : ℂ)^2/2))) :=
  Complex.continuous_exp.continuousAt.tendsto.comp (gaussian_exponent_tendsto hv t)

end Luce.BernoulliCLT
