import Luce.Section6LocalCoefficientComparison
import Luce.Section6CrossDepthAlgebra

noncomputable section
namespace Luce.Section6

theorem absolute_error_of_relative {z D eps : ℝ} (hD : 0 < D)
    (herr : |z/D-1| ≤ eps) : |z-D| ≤ D*eps := by
  rw [div_sub_one hD.ne', abs_div, abs_of_pos hD] at herr
  have h := (div_le_iff₀ hD).mp herr
  simpa only [mul_comm] using h

/-- The complete deterministic one-edge step. The four relative errors
are the two profile errors and the actual time/weight event. -/
theorem normalized_local_pointwise {theta t mu T W q gamma h x eps xi : ℝ}
    (htheta : 0 < theta) (ht : 0 < t) (hmu : 0 < mu) (hW : 0 < W)
    (hq : 0 < q) (hg : 0 < gamma) (hh : 0 < h) (hx : 0 < x)
    (he : 0 ≤ eps) (heSmall : eps ≤ 1/16) (hxi : 0 ≤ xi)
    (htarget : |theta*t/(q*x)-1| ≤ eps)
    (hhazard : |(theta/mu)/(gamma*q*x/h)-1| ≤ eps)
    (htime : |T/t-1| ≤ eps) (hweight : |W/mu-1| ≤ eps) :
    let C := 1+22*gamma*q+16*gamma^2*q
    let H := x/h*Real.exp (-(q*x/4))
    let K := gamma*q*x/h*Real.exp (-(q*x))
    0 ≤ K ∧ K ≤ C*H ∧
    exponentialGapMass theta T (xi/W) ≤ C*H*xi ∧
    |exponentialGapMass theta T (xi/W)-K*xi| ≤ C*H*(eps*xi+xi^2/h) := by
  dsimp only
  let C := 1+22*gamma*q+16*gamma^2*q
  let H := x/h*Real.exp (-(q*x/4))
  let K := gamma*q*x/h*Real.exp (-(q*x))
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hc2 : 2*gamma*q ≤ C := by dsimp [C]; nlinarith [sq_nonneg gamma, mul_pos hg hq]
  have hc20 : 20*gamma*q ≤ C := by dsimp [C]; nlinarith [sq_nonneg gamma, mul_pos hg hq]
  have hc16 : 16*gamma^2*q ≤ C := by dsimp [C]; nlinarith [mul_pos hg hq]
  have htime' := relative_product_error (a := 1) (b := 1) zero_le_one zero_le_one he
    (by linarith : eps ≤ 2) (by simpa using htarget) (by simpa using htime)
  have htid : (theta*t/(q*x))*(T/t) = theta*T/(q*x) := by field_simp
  rw [htid] at htime'
  norm_num only at htime'
  have hweight' := relative_quotient_error (a := 1) (b := 1) zero_le_one zero_le_one he
    (by simpa using hhazard) (by simpa using hweight) (by simpa using (show eps ≤ 1/2 by linarith))
  have hwid : ((theta/mu)/(gamma*q*x/h))/(W/mu) = (theta/W)/(gamma*q*x/h) := by field_simp
  rw [hwid] at hweight'
  norm_num only at hweight'
  have hyerr := absolute_error_of_relative (mul_pos hq hx) htime'
  have hberr := absolute_error_of_relative (by positivity : 0 < gamma*q*x/h) hweight'
  have hy : q*x/2 ≤ theta*T := by
    have hh' := (abs_le.mp hyerr).1
    have hsmall := mul_le_mul_of_nonneg_left heSmall (mul_pos hq hx).le
    nlinarith only [hh', hsmall, mul_pos hq hx]
  have hbounds := local_gap_coefficient_bounds hq hg hh hx (div_pos htheta hW).le
    (by positivity : 0 ≤ 4*eps) (by linarith : 4*eps ≤ 1) hy hberr hyerr
  have hexp : survivalKernel T theta = Real.exp (-(theta*T)) := by unfold survivalKernel; congr 1; ring
  have hbcoef : (theta/W)*survivalKernel T theta ≤ C*H := by
    rw [hexp]
    exact hbounds.1.trans (mul_le_mul_of_nonneg_right hc2 hH)
  have hKB : K ≤ C*H := by
    have hdecay : Real.exp (-(q*x)) ≤ Real.exp (-(q*x/4)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_pos hq hx])
    calc
      _ ≤ (gamma*q)*(x/h*Real.exp (-(q*x/4))) := by
        dsimp only [K]
        have hh' := mul_le_mul_of_nonneg_left hdecay (by positivity : 0 ≤ gamma*q*x/h)
        exact hh'.trans_eq (by ring)
      _ ≤ C*H := mul_le_mul_of_nonneg_right (by nlinarith [mul_pos hg hq, hc2]) hH
  have hcoeferr : |(theta/W)*survivalKernel T theta-K| ≤ C*H*eps := by
    rw [hexp]
    calc
      _ ≤ (5*gamma*q)*H*(4*eps) := hbounds.2.1
      _ = (20*gamma*q)*H*eps := by ring
      _ ≤ C*H*eps := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc20 hH) he
  have hrem : (theta/W)^2*survivalKernel T theta ≤ C*H/h := by
    rw [hexp]
    exact hbounds.2.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc16 hH) hh.le)
  have hfinal := normalized_gap_comparison htheta.le hW hxi hK hbcoef hKB hcoeferr hrem
  refine ⟨hK, hKB, hfinal.2.1, ?_⟩
  exact hfinal.2.2.2.2.trans_eq (by ring)

end Luce.Section6
