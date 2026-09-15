import Luce.Section6FastArrivalBounds

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Luce.Section6

theorem fast_arrival_boundary_hasDerivAt {alpha r s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun x : ℝ => x*(1-Real.exp (-(r*x^(-alpha)))))
      ((1-Real.exp (-(r*s^(-alpha)))) -
        (r*alpha)*(s^(-alpha)*Real.exp (-(r*s^(-alpha))))) s := by
  have hd := (hasDerivAt_id s).mul ((hasDerivAt_const s (1 : ℝ)).sub
    (((Real.hasDerivAt_rpow_const (p := -alpha) (Or.inl hs.ne')).const_mul r).neg.exp))
  have hp : s*s^(-alpha-1) = s^(-alpha) := by
    conv_lhs => lhs; rw [← Real.rpow_one s]
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have he : 1*(1-Real.exp (-(r*s^(-alpha)))) +
      s*(0-Real.exp (-(r*s^(-alpha)))*(-(r*((-alpha)*s^(-alpha-1))))) =
      (1-Real.exp (-(r*s^(-alpha)))) -
        (r*alpha)*(s^(-alpha)*Real.exp (-(r*s^(-alpha)))) := by
    calc
      _ = (1-Real.exp (-(r*s^(-alpha)))) -
          (r*alpha)*((s*s^(-alpha-1))*Real.exp (-(r*s^(-alpha)))) := by ring
      _ = _ := by rw [hp]
  simp only [Pi.sub_apply, Pi.neg_apply, id_eq] at hd
  rw [he] at hd
  exact hd

/-- The fast-arrival Gamma integral, derived by integration by parts.
Integrability and both boundary limits are proved before applying FTC. -/
theorem integral_fast_arrival {alpha r : ℝ} (ha : 1 < alpha) (hr : 0 < r) :
    (∫ s in Ioi (0 : ℝ), 1-Real.exp (-(r*s^(-alpha)))) =
      r^(1/alpha)*Real.Gamma (1-1/alpha) := by
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  have hp : (-alpha : ℝ) ≠ 0 := neg_ne_zero.mpr ha0.ne'
  have hexp : (-alpha+1)/(-alpha) = 1-1/alpha := by field_simp; ring
  have hgamma : 0 < (-alpha+1)/(-alpha) := div_pos_of_neg_of_neg (by linarith) (by linarith)
  have hi := integrableOn_fast_arrival ha hr
  have hj := integrableOn_power_exp (a := -alpha) hp hr hgamma
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (fast_arrival_boundary_continuous (alpha := alpha) hr)
    (fun s hs => fast_arrival_boundary_hasDerivAt (alpha := alpha) (r := r) hs)
    (hi.sub (hj.const_mul (r*alpha))) (fast_arrival_boundary_tendsto ha hr)
  rw [integral_sub hi (hj.const_mul (r*alpha)), integral_const_mul,
    integral_power_exp hp hr hgamma, abs_neg, abs_of_pos ha0] at hFTC
  simp only [zero_mul, sub_zero] at hFTC
  have hmul : (r*alpha)*((1/r)^((-alpha+1)/(-alpha))*Real.Gamma ((-alpha+1)/(-alpha))/alpha) =
      r^(1/alpha)*Real.Gamma (1-1/alpha) := by
    rw [hexp, Real.div_rpow zero_le_one hr.le, Real.one_rpow, Real.rpow_sub hr,
      Real.rpow_one]
    field_simp
  rw [hmul] at hFTC
  exact sub_eq_zero.mp hFTC

end Luce.Section6
