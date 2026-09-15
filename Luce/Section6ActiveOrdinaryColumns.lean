import Luce.Section6PowerWeightedSum
import Luce.Section6ActiveOrdinaryRows

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The numerator column sum at target depth t, covering both signed-power
cases whenever the manuscript's column integral is finite. -/
theorem ordinary_power_column_bound {p d : ℝ} (hp : p ≠ 0)
    (hq : 0 < (p+1)/p) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/t)^p*Real.exp (-(d*((h : ℝ)/t)^p))) ≤ C*t := by
  obtain ⟨C, hC, hb⟩ := power_weighted_positive_sum_bound (a := p) hp hq hd
  refine ⟨C, hC, ?_⟩
  intro t ht M
  have hscale : (t^(-p))^(1-(p+1)/p) = t := by
    rw [← Real.rpow_mul ht.le]
    have he : (-p)*(1-(p+1)/p) = 1 := by field_simp; ring
    rw [he, Real.rpow_one]
  have hs := hb (t^(-p)) (Real.rpow_pos_of_pos ht _) M
  rw [hscale] at hs
  have he : (∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/t)^p*Real.exp (-(d*((h : ℝ)/t)^p))) =
      ∑ h ∈ Finset.Ico 1 (M+1), t^(-p)*(h : ℝ)^p*Real.exp (-(d*t^(-p)*(h : ℝ)^p)) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr (by have := (Finset.mem_Ico.mp hh).1; omega)
    have hid : ((h : ℝ)/t)^p = t^(-p)*(h : ℝ)^p := by
      rw [Real.div_rpow hh0.le ht.le, Real.rpow_neg ht.le]
      ring
    rw [hid]
    simp only [mul_assoc]
  rw [he]
  exact hs

theorem right_ordinary_column_bound {beta d : ℝ} (hb : 0 < beta) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/t)^beta*Real.exp (-(d*((h : ℝ)/t)^beta))) ≤ C*t :=
  ordinary_power_column_bound hb.ne' (div_pos (by linarith) hb) hd

theorem left_ordinary_column_bound {alpha d : ℝ} (ha : 1 < alpha) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), (t/(h : ℝ))^alpha*Real.exp (-(d*(t/(h : ℝ))^alpha))) ≤ C*t := by
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  obtain ⟨C, hC, hb⟩ := ordinary_power_column_bound (p := -alpha) (neg_ne_zero.mpr ha0.ne')
    (div_pos_of_neg_of_neg (by linarith) (by linarith)) hd
  refine ⟨C, hC, ?_⟩
  intro t ht M
  have he : (∑ h ∈ Finset.Ico 1 (M+1), (t/(h : ℝ))^alpha*Real.exp (-(d*(t/(h : ℝ))^alpha))) =
      ∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/t)^(-alpha)*Real.exp (-(d*((h : ℝ)/t)^(-alpha))) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr (by have := (Finset.mem_Ico.mp hh).1; omega)
    rw [reverse_ratio_power ht hh0]
  rw [he]
  exact hb t ht M

end Luce.Section6
