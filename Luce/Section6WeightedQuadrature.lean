import Luce.Section6UnimodalQuadrature
import Luce.Section6PopulationFinite
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem rateKernel_monotone_before_peak {t : ℝ} (ht : 0 < t) :
    MonotoneOn (rateKernel t) (Iic (1/t)) := by
  have hf : Differentiable ℝ (rateKernel t) := fun x => (hasDerivAt_rateKernel t x).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Iic _) hf.continuous.continuousOn hf.differentiableOn
  intro x hx
  rw [(hasDerivAt_rateKernel t x).deriv]
  have hx' : x ≤ 1/t := (interior_subset : interior (Iic (1/t)) ⊆ Iic (1/t)) hx
  have hb : t*x ≤ 1 := by have := (le_div_iff₀ ht).mp hx'; nlinarith
  exact mul_nonneg (sub_nonneg.mpr hb) (survivalKernel_pos _ _).le

theorem rateKernel_antitone_after_peak {t : ℝ} (ht : 0 < t) :
    AntitoneOn (rateKernel t) (Ici (1/t)) := by
  have hf : Differentiable ℝ (rateKernel t) := fun x => (hasDerivAt_rateKernel t x).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) hf.continuous.continuousOn hf.differentiableOn
  intro x hx
  rw [(hasDerivAt_rateKernel t x).deriv]
  have hx' : 1/t ≤ x := (interior_subset : interior (Ici (1/t)) ⊆ Ici (1/t)) hx
  have hb : 1 ≤ t*x := by have := (div_le_iff₀ ht).mp hx'; nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) (survivalKernel_pos _ _).le

/-- Exact weighted-kernel quadrature for either manuscript grid. The error
is O(1/(n*t)), uniformly in the leading rate coefficient and the power. -/
theorem weighted_power_quadrature (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {beta c t : ℝ} (hb : 0 < beta) (hc : 0 < c) (ht : 0 < t) :
    |(∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^beta))/(n : ℝ) -
      ∫ s in (0 : ℝ)..1, rateKernel t (c*s^beta)| ≤
      (2*(Real.exp (-1)/t))/(n : ℝ) := by
  let R : ℝ := (1/(c*t))^(1/beta)
  have hRpos : 0 < R := Real.rpow_pos_of_pos (by positivity) _
  have hR : c*R^beta = 1/t := by
    dsimp [R]
    rw [one_div beta, Real.rpow_inv_rpow (by positivity : (0 : ℝ) ≤ 1/(c*t)) hb.ne']
    field_simp
  let q := min R 1
  have hq0 : 0 ≤ q := le_min hRpos.le zero_le_one
  have hq1 : q ≤ 1 := min_le_right _ _
  have hqR : q ≤ R := min_le_left _ _
  have hup : MonotoneOn (fun s => rateKernel t (c*s^beta)) (Icc 0 q) := by
    intro x hx y hy hxy
    have hxB : c*x^beta ≤ 1/t := by
      rw [← hR]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.1 (hx.2.trans hqR) hb.le) hc.le
    have hyB : c*y^beta ≤ 1/t := by
      rw [← hR]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.1 (hy.2.trans hqR) hb.le) hc.le
    exact rateKernel_monotone_before_peak ht hxB hyB
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.1 hxy hb.le) hc.le)
  have hdown : AntitoneOn (fun s => rateKernel t (c*s^beta)) (Icc q 1) := by
    intro x hx y hy hxy
    by_cases hR1 : R ≤ 1
    · have hq : q = R := min_eq_left hR1
      have hx0 : 0 ≤ x := hq0.trans hx.1
      have hxB : 1/t ≤ c*x^beta := by
        rw [← hR]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hRpos.le (by simpa [hq] using hx.1) hb.le) hc.le
      have hyB : 1/t ≤ c*y^beta := by
        rw [← hR]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hRpos.le (by simpa [hq] using hy.1) hb.le) hc.le
      exact rateKernel_antitone_after_peak ht hxB hyB
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hxy hb.le) hc.le)
    · have hq : q = 1 := min_eq_right (le_of_not_ge hR1)
      have hx1 : x = 1 := le_antisymm hx.2 (by simpa [hq] using hx.1)
      have hy1 : y = 1 := le_antisymm hy.2 (by simpa [hq] using hy.1)
      simp [hx1, hy1]
  have h := unimodal_sample_average_error grid hn hq0 hq1 hup hdown
  apply h.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hmax := rateKernel_le_exp_neg_one_div (a := c*q^beta) ht
  have hz : 0 ≤ rateKernel t (c*(0 : ℝ)^beta) := rateKernel_nonneg (by positivity)
  have ho : 0 ≤ rateKernel t (c*(1 : ℝ)^beta) := rateKernel_nonneg (by positivity)
  linarith

end Luce.Section6
