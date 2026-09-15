import Luce.Section6NormalizedGapTaylor

noncomputable section
namespace Luce.Section6

theorem linear_exponential_bound {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x*Real.exp (-(c*x)) ≤ 1/c := by
  have he : c*x ≤ Real.exp (c*x) := by linarith [Real.add_one_le_exp (c*x)]
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(c*x))).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hh
  apply (le_div_iff₀ hc).mpr
  nlinarith only [hh]

/-- The exponential slack absorbs the corner ratio, uniformly down to
ratio zero. -/
theorem local_coefficient_slack {q x : ℝ} (hq : 0 < q) (hx : 0 ≤ x) :
    (1+q*x)*Real.exp (-(q*x/2)) ≤ 5*Real.exp (-(q*x/4)) ∧
    x*Real.exp (-(q*x/2)) ≤ (4/q)*Real.exp (-(q*x/4)) := by
  have hsplit : Real.exp (-(q*x/2)) = Real.exp (-(q*x/4))*Real.exp (-(q*x/4)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlin : x*Real.exp (-(q*x/4)) ≤ 4/q := by
    convert linear_exponential_bound (c := q/4) (by positivity) hx using 1 <;> ring_nf
  have hsmall : Real.exp (-(q*x/4)) ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (by positivity))
  have hqx : q*(x*Real.exp (-(q*x/4))) ≤ 4 := by
    calc
      _ ≤ q*(4/q) := mul_le_mul_of_nonneg_left hlin hq.le
      _ = 4 := by field_simp
  rw [hsplit]
  constructor
  · calc
      _ = (Real.exp (-(q*x/4))+q*(x*Real.exp (-(q*x/4))))*Real.exp (-(q*x/4)) := by ring
      _ ≤ 5*Real.exp (-(q*x/4)) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-(q*x/4))).le

/-- Deterministic coefficient comparison in the physical target scale.
The premises will be supplied by profile asymptotics and the actual
time/weight event. The decay loss absorbs all extra ratio factors. -/
theorem local_gap_coefficient_bounds {q gamma h x y b eps : ℝ}
    (hq : 0 < q) (hg : 0 < gamma) (hh : 0 < h) (hx : 0 < x)
    (hb : 0 ≤ b) (he : 0 ≤ eps) (he1 : eps ≤ 1)
    (hy : q*x/2 ≤ y)
    (hberr : |b-gamma*q*x/h| ≤ (gamma*q*x/h)*eps)
    (hyerr : |y-q*x| ≤ q*x*eps) :
    b*Real.exp (-y) ≤ (2*gamma*q)*(x/h*Real.exp (-(q*x/4))) ∧
    |b*Real.exp (-y)-(gamma*q*x/h)*Real.exp (-(q*x))| ≤
      (5*gamma*q)*(x/h*Real.exp (-(q*x/4)))*eps ∧
    b^2*Real.exp (-y) ≤ (16*gamma^2*q)*(x/h*Real.exp (-(q*x/4)))/h := by
  let B := gamma*q*x/h
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbB : b ≤ 2*B := by
    have hrel := (abs_le.mp hberr).2
    have heB := mul_le_mul_of_nonneg_left he1 hB
    dsimp [B] at *
    nlinarith only [hrel, heB]
  have hdecay : Real.exp (-y) ≤ Real.exp (-(q*x/2)) := Real.exp_le_exp.mpr (by linarith)
  have hweak : Real.exp (-(q*x/2)) ≤ Real.exp (-(q*x/4)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_pos hq hx])
  have hdiff : |Real.exp (-y)-Real.exp (-(q*x))| ≤
      Real.exp (-(q*x/2))*(q*x*eps) := by
    have hd := survivalKernel_sub_bound_with_decay (t := 1) (by norm_num) hy
      (show q*x/2 ≤ q*x by nlinarith [mul_pos hq hx])
    simp only [survivalKernel, neg_mul, one_mul] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left hyerr (Real.exp_pos _).le)
  have hslack := local_coefficient_slack hq hx.le
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ (2*B)*Real.exp (-(q*x/4)) :=
        mul_le_mul hbB (hdecay.trans hweak) (Real.exp_pos _).le (by positivity)
      _ = _ := by dsimp [B]; ring
  · calc
      _ = |(b-B)*Real.exp (-y)+B*(Real.exp (-y)-Real.exp (-(q*x)))| := by
        dsimp [B]
        congr 1
        ring
      _ ≤ |b-B| * Real.exp (-y)+B*|Real.exp (-y)-Real.exp (-(q*x))| := by
        simpa only [abs_mul, abs_of_pos (Real.exp_pos (-y)), abs_of_nonneg hB] using
          abs_add_le ((b-B)*Real.exp (-y)) (B*(Real.exp (-y)-Real.exp (-(q*x))))
      _ ≤ (B*eps)*Real.exp (-(q*x/2))+B*(Real.exp (-(q*x/2))*(q*x*eps)) :=
        add_le_add (mul_le_mul hberr hdecay (Real.exp_pos _).le (mul_nonneg hB he))
          (mul_le_mul_of_nonneg_left hdiff hB)
      _ = B*((1+q*x)*Real.exp (-(q*x/2)))*eps := by ring
      _ ≤ B*(5*Real.exp (-(q*x/4)))*eps := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hslack.1 hB) he
      _ = _ := by dsimp [B]; ring
  · calc
      _ ≤ (2*B)^2*Real.exp (-(q*x/2)) :=
        mul_le_mul (pow_le_pow_left₀ hb hbB 2) hdecay (Real.exp_pos _).le (sq_nonneg _)
      _ = (4*gamma^2*q^2*x/h^2)*(x*Real.exp (-(q*x/2))) := by dsimp [B]; ring
      _ ≤ (4*gamma^2*q^2*x/h^2)*((4/q)*Real.exp (-(q*x/4))) :=
        mul_le_mul_of_nonneg_left hslack.2 (by positivity)
      _ = _ := by field_simp; ring

end Luce.Section6
