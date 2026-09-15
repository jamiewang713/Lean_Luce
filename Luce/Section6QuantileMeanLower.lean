import Luce.Section6DeletedQuantileSeparation
import Luce.Section6LocalCoefficientComparison

noncomputable section
namespace Luce.Section6

/-- The arrival mean remains of order the target depth throughout a
small relative time window, even after finitely many deletions. -/
theorem deleted_arrival_window_mean_lower {n r : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (hr : removed.card ≤ r)
    {m t u C : ℝ} (hm : 0 < m) (ht : 0 < t) (hu : 0 < u) (hu1 : u ≤ 1/2)
    (hCu : C*u ≤ 1/4) (hrm : (r : ℝ) ≤ m/4)
    (hcentral : (n : ℝ)*populationG w t = m)
    (hupper : (n : ℝ)*populationD w 1 ((1-u)*t) ≤ C*m/t) :
    m/2 ≤ (n : ℝ)*deletedG w removed ((1-u)*t) ∧
    m/2 ≤ (n : ℝ)*deletedG w removed ((1+u)*t) := by
  have hlo : 0 ≤ (1-u)*t := mul_nonneg (by linarith) ht.le
  have hhi : 0 ≤ (1+u)*t := by positivity
  have horder : (1-u)*t ≤ t := by nlinarith [mul_pos hu ht]
  have hsep := (populationG_separation hn w horder).2
  have hsep' := mul_le_mul_of_nonneg_left hsep (Nat.cast_nonneg n)
  have hupper' := mul_le_mul_of_nonneg_right hupper (mul_pos hu ht).le
  have hid : (C*m/t)*(u*t) = (C*u)*m := by field_simp
  rw [hid] at hupper'
  have hscale := mul_le_mul_of_nonneg_right hCu hm.le
  have hdel := scaled_deletion_error hn (populationG_deletion_bound w removed hr hlo)
  have hdel' := (abs_le.mp hdel).2
  have hlower : m/2 ≤ (n : ℝ)*deletedG w removed ((1-u)*t) := by
    nlinarith only [hcentral, hsep', hupper', hscale, hdel', hrm]
  refine ⟨hlower, hlower.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  unfold deletedG
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro i _
  have he := survivalKernel_antitone_time (w.positive i).le
    (show (1-u)*t ≤ (1+u)*t by nlinarith [mul_pos hu ht])
  linarith

/-- The corresponding survivor-mean lower bounds at the right corner. -/
theorem deleted_survivor_window_mean_lower {n r : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (hr : removed.card ≤ r)
    {m t u C : ℝ} (hm : 0 < m) (ht : 0 < t) (hu : 0 < u) (hu1 : u ≤ 1/2)
    (hCu : C*u ≤ 1/4) (hrm : (r : ℝ) ≤ m/4)
    (hcentral : (n : ℝ)*populationH w t = m)
    (hupper : (n : ℝ)*populationD w 1 t ≤ C*m/t) :
    m/2 ≤ (n : ℝ)*deletedH w removed ((1-u)*t) ∧
    m/2 ≤ (n : ℝ)*deletedH w removed ((1+u)*t) := by
  have hhi : 0 ≤ (1+u)*t := by positivity
  have horder : t ≤ (1+u)*t := by nlinarith [mul_pos hu ht]
  have hsep := (populationH_separation hn w horder).2
  have hsep' := mul_le_mul_of_nonneg_left hsep (Nat.cast_nonneg n)
  have hupper' := mul_le_mul_of_nonneg_right hupper (mul_pos hu ht).le
  have hid : (C*m/t)*(u*t) = (C*u)*m := by field_simp
  rw [hid] at hupper'
  have hscale := mul_le_mul_of_nonneg_right hCu hm.le
  have hdel := scaled_deletion_error hn (populationH_deletion_bound w removed hr hhi)
  have hdel' := (abs_le.mp hdel).2
  have hlower : m/2 ≤ (n : ℝ)*deletedH w removed ((1+u)*t) := by
    nlinarith only [hcentral, hsep', hupper', hscale, hdel', hrm]
  refine ⟨?_, hlower⟩
  apply hlower.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  unfold deletedH
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro i _
  exact survivalKernel_antitone_time (w.positive i).le
    (show (1-u)*t ≤ (1+u)*t by nlinarith [mul_pos hu ht])

/-- Convert the already proved exponential count tail to the polynomial
scale needed for the normalized-gap argument. -/
theorem quantile_exponential_tail_le_polynomial {a u m mean : ℝ}
    (ha : 0 < a) (hu : 0 < u) (hm : 0 < m) (hmean : m/2 ≤ mean) :
    Real.exp (-(a*u/8)^2*mean/4) ≤ (512/a^2)/(u^2*m) := by
  have hdecay : Real.exp (-(a*u/8)^2*mean/4) ≤ Real.exp (-(a^2*u^2*m/512)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hmean (sq_nonneg (a*u/8))
    nlinarith only [hmul]
  have hz : 0 < a^2*u^2*m/512 := by positivity
  have hlin := linear_exponential_bound (c := 1) zero_lt_one hz.le
  simp only [one_mul, div_one] at hlin
  have hb : Real.exp (-(a^2*u^2*m/512)) ≤ 1/(a^2*u^2*m/512) :=
    (le_div_iff₀ hz).mpr (by simpa only [mul_comm] using hlin)
  exact (hdecay.trans hb).trans_eq (by field_simp)

end Luce.Section6
