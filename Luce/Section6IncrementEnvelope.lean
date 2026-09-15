import Luce.Section6IncrementDensity

noncomputable section
open MeasureTheory
namespace Luce.Section6

theorem incrementDensity_deriv_bound {gamma q : ℝ} (hg : 0 < gamma) (hq : 0 < q) (x : ℝ) :
    ‖deriv (incrementDensity gamma q) x‖ ≤
      gamma*incrementDensity gamma q x*(1+q*Real.exp (gamma*x)) := by
  rw [(incrementDensity_hasDerivAt gamma q x).deriv, Real.norm_eq_abs, abs_mul,
    abs_of_pos (mul_pos hg (incrementDensity_pos hg hq x))]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hg.le (incrementDensity_pos hg hq x).le)
  have hh := abs_sub_le (1 : ℝ) 0 (q*Real.exp (gamma*x))
  simpa only [sub_zero, zero_sub, abs_neg, abs_one,
    abs_of_pos (mul_pos hq (Real.exp_pos _))] using hh

/-- The explicit density and its derivative have a common two-sided
exponential envelope. This is the quantitative analytic input to the grid
comparison; it is proved from gamma>0 and q>0. -/
theorem incrementDensity_exponential_envelope {gamma q : ℝ}
    (hg : 0 < gamma) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      incrementDensity gamma q x + ‖deriv (incrementDensity gamma q) x‖ ≤
        C*Real.exp (-gamma*|x|) := by
  obtain ⟨B, hB, hb⟩ := exists_power_exp_bound (a := 2) (by norm_num)
  obtain ⟨D, hD, hd⟩ := exists_power_exp_bound (a := 3) (by norm_num)
  let C := gamma*q + gamma^2*q*(1+q) + gamma/q*B + gamma^2/q*(B+D)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x
  let t := q*Real.exp (gamma*x)
  have ht : 0 < t := mul_pos hq (Real.exp_pos _)
  have hp := (incrementDensity_pos hg hq x).le
  have hdb := incrementDensity_deriv_bound hg hq x
  have hweighted : (incrementDensity gamma q x + ‖deriv (incrementDensity gamma q) x‖)*
      Real.exp (gamma*|x|) ≤ C := by
    by_cases hx : x ≤ 0
    · have htx : t ≤ q := by
        apply mul_le_of_le_one_right hq.le
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hg.le hx)
      have he : incrementDensity gamma q x*Real.exp (gamma*|x|) =
          gamma*q*Real.exp (-t) := by
        rw [abs_of_nonpos hx]
        have hc : Real.exp (gamma*x)*Real.exp (-(gamma*x)) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        calc
          _ = gamma*q*(Real.exp (gamma*x)*Real.exp (-(gamma*x)))*Real.exp (-t) := by
            dsimp [incrementDensity, t]
            simp only [mul_neg, neg_mul]
            ring
          _ = _ := by rw [hc]; ring
      have hpb : incrementDensity gamma q x*Real.exp (gamma*|x|) ≤ gamma*q := by
        rw [he]
        exact mul_le_of_le_one_right (mul_nonneg hg.le hq.le)
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le))
      have hdd : ‖deriv (incrementDensity gamma q) x‖*Real.exp (gamma*|x|) ≤
          gamma^2*q*(1+q) := by
        calc
          _ ≤ gamma*(incrementDensity gamma q x*Real.exp (gamma*|x|))*(1+t) := by
            convert mul_le_mul_of_nonneg_right hdb (Real.exp_pos (gamma*|x|)).le using 1 <;>
              first | rfl | ring
          _ ≤ gamma*(gamma*q)*(1+q) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpb hg.le) (by linarith)
              (by positivity) (by positivity)
          _ = _ := by ring
      rw [add_mul]
      have hrest : 0 ≤ gamma/q*B + gamma^2/q*(B+D) := by positivity
      dsimp [C]
      simp only [Real.norm_eq_abs] at hdd
      linarith
    · have hx0 : 0 ≤ x := (lt_of_not_ge hx).le
      have he : incrementDensity gamma q x*Real.exp (gamma*|x|) =
          gamma/q*(t^2*Real.exp (-t)) := by
        rw [abs_of_nonneg hx0]
        dsimp [incrementDensity, t]
        simp only [neg_mul]
        field_simp
      have htB : t^2*Real.exp (-t) ≤ B := by
        simpa only [Real.rpow_two] using hb t ht.le
      have htD : t^3*Real.exp (-t) ≤ D := by
        simpa only [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using hd t ht.le
      have hpb : incrementDensity gamma q x*Real.exp (gamma*|x|) ≤ gamma/q*B := by
        rw [he]
        exact mul_le_mul_of_nonneg_left htB (by positivity)
      have hdd : ‖deriv (incrementDensity gamma q) x‖*Real.exp (gamma*|x|) ≤
          gamma^2/q*(B+D) := by
        calc
          _ ≤ gamma*(incrementDensity gamma q x*Real.exp (gamma*|x|))*(1+t) := by
            convert mul_le_mul_of_nonneg_right hdb (Real.exp_pos (gamma*|x|)).le using 1 <;>
              first | rfl | ring
          _ = gamma^2/q*(t^2*Real.exp (-t)+t^3*Real.exp (-t)) := by rw [he]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add htB htD) (by positivity)
      rw [add_mul]
      have hrest : 0 ≤ gamma*q + gamma^2*q*(1+q) := by positivity
      dsimp [C]
      simp only [Real.norm_eq_abs] at hdd
      linarith
  have hh := mul_le_mul_of_nonneg_right hweighted (Real.exp_pos (-gamma*|x|)).le
  have hc : Real.exp (gamma*|x|)*Real.exp (-gamma*|x|) = 1 := by
    rw [← Real.exp_add]
    have he : gamma*|x| + -gamma*|x| = 0 := by ring
    rw [he, Real.exp_zero]
  rw [mul_assoc, hc, mul_one] at hh
  exact hh

theorem incrementDensity_deriv_continuous (gamma q : ℝ) :
    Continuous (fun x => deriv (incrementDensity gamma q) x) := by
  have he (x : ℝ) := (incrementDensity_hasDerivAt gamma q x).deriv
  simp_rw [he]
  unfold incrementDensity
  fun_prop

/-- A genuine exponential moment for the common density/derivative
envelope, including integrability rather than merely a formal integral. -/
theorem incrementDensity_exponential_moment {gamma q : ℝ}
    (hg : 0 < gamma) (hq : 0 < q) :
    Integrable (fun x : ℝ => Real.exp ((gamma/2)*|x|)*
      (incrementDensity gamma q x + ‖deriv (incrementDensity gamma q) x‖)) := by
  obtain ⟨C, hC, hb⟩ := incrementDensity_exponential_envelope hg hq
  have hdom := (integrable_exp_neg_abs68 (half_pos hg)).const_mul C
  have hmeas : Continuous (fun x : ℝ => Real.exp ((gamma/2)*|x|)*
      (incrementDensity gamma q x + ‖deriv (incrementDensity gamma q) x‖)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      ((incrementDensity_continuous gamma q).add (incrementDensity_deriv_continuous gamma q).norm)
  apply hdom.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with x
  have hp := (incrementDensity_pos hg hq x).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (hb x) (Real.exp_pos _).le).trans_eq
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

end Luce.Section6
