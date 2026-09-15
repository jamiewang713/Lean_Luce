import Luce.Section6PowerDensitySum

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem scaled_power_density_factor {n h : ℝ} (hn : 0 < n) (hh : 0 < h)
    (theta p d : ℝ) :
    (theta*(h/n)^p/h)*Real.exp (-(d*(theta*(h/n)^p))) =
      (theta/n^p)*h^(p-1)*Real.exp (-(d*(theta/n^p)*h^p)) := by
  have he : theta*(h/n)^p = (theta/n^p)*h^p := by
    rw [Real.div_rpow hh.le hn.le]
    ring
  rw [he]
  have hpref : ((theta/n^p)*h^p)/h = (theta/n^p)*h^(p-1) := by
    rw [Real.rpow_sub hh, Real.rpow_one]
    ring
  rw [hpref]
  simp only [mul_assoc]

/-- Uniform ordinary row sums for the forward ratio and every nonzero
power. In particular, p=alpha gives the active-left manuscript kernel. -/
theorem scaled_power_kernel_row_bound {p d : ℝ} (hp : p ≠ 0) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n theta : ℝ), 0 < n → 0 < theta → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), (theta*((h : ℝ)/n)^p/(h : ℝ))*
      Real.exp (-(d*(theta*((h : ℝ)/n)^p)))) ≤ C := by
  obtain ⟨C, hC, hb⟩ := power_density_positive_sum_bound hp hd
  refine ⟨C, hC, ?_⟩
  intro n theta hn ht M
  have he : (∑ h ∈ Finset.Ico 1 (M+1), (theta*((h : ℝ)/n)^p/(h : ℝ))*
      Real.exp (-(d*(theta*((h : ℝ)/n)^p)))) =
      ∑ h ∈ Finset.Ico 1 (M+1), (theta/n^p)*(h : ℝ)^(p-1)*
        Real.exp (-(d*(theta/n^p)*(h : ℝ)^p)) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr (by have := (Finset.mem_Ico.mp hh).1; omega)
    exact scaled_power_density_factor hn hh0 theta p d
  rw [he]
  exact hb (theta/n^p) (by positivity) M

theorem reverse_ratio_power {n h : ℝ} (hn : 0 < n) (hh : 0 < h) (p : ℝ) :
    (n/h)^p = (h/n)^(-p) := by
  rw [Real.rpow_neg_eq_inv_rpow]
  congr 1
  field_simp

/-- The active-right ordinary row sum in its original inverse-ratio form.
No upper or lower bound on the positive source rate is assumed. -/
theorem inverse_power_kernel_row_bound {beta d : ℝ} (hb : 0 < beta) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n theta : ℝ), 0 < n → 0 < theta → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), (theta*(n/(h : ℝ))^beta/(h : ℝ))*
      Real.exp (-(d*(theta*(n/(h : ℝ))^beta)))) ≤ C := by
  obtain ⟨C, hC, hs⟩ := scaled_power_kernel_row_bound (p := -beta) (neg_ne_zero.mpr hb.ne') hd
  refine ⟨C, hC, ?_⟩
  intro n theta hn ht M
  have he : (∑ h ∈ Finset.Ico 1 (M+1), (theta*(n/(h : ℝ))^beta/(h : ℝ))*
      Real.exp (-(d*(theta*(n/(h : ℝ))^beta)))) =
      ∑ h ∈ Finset.Ico 1 (M+1), (theta*((h : ℝ)/n)^(-beta)/(h : ℝ))*
        Real.exp (-(d*(theta*((h : ℝ)/n)^(-beta)))) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr (by have := (Finset.mem_Ico.mp hh).1; omega)
    rw [reverse_ratio_power hn hh0]
  rw [he]
  exact hs n theta hn ht M

end Luce.Section6
