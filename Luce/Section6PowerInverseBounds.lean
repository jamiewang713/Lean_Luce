import Luce.Section6PopulationMomentBounds

noncomputable section
open Set
namespace Luce.Section6

/-- A power has a uniform linear perturbation bound on [1/2,2].
The constant is constructed from its derivative, for either sign of r. -/
theorem rpow_relative_lipschitz (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (1/2 : ℝ) 2,
      |x^r-1| ≤ C*|x-1| := by
  let B := (1/2 : ℝ)^(r-1)+(2 : ℝ)^(r-1)
  have hB : 0 < B := add_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (by norm_num) _)
  let C := |r| * B+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hpow (y : ℝ) (hy : y ∈ Icc (1/2 : ℝ) 2) : y^(r-1) ≤ B := by
    have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
    by_cases hr : 0 ≤ r-1
    · have hh := Real.rpow_le_rpow hy0.le hy.2 hr
      dsimp [B]
      linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) (r-1)]
    · have hh := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1/2) hy.1 (le_of_not_ge hr)
      dsimp [B]
      linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (r-1)]
  have hderiv (y : ℝ) (hy : y ∈ Icc (1/2 : ℝ) 2) :
      HasDerivWithinAt (fun z : ℝ => z^r) (r*y^(r-1)) (Icc (1/2 : ℝ) 2) y :=
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) hy.1)))).hasDerivWithinAt
  have hnorm (y : ℝ) (hy : y ∈ Icc (1/2 : ℝ) 2) : ‖r*y^(r-1)‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos
      (lt_of_lt_of_le (by norm_num) hy.1) _)]
    have hh := mul_le_mul_of_nonneg_left (hpow y hy) (abs_nonneg r)
    dsimp [C]
    linarith
  have hh := (convex_Icc (1/2 : ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z : ℝ => z^r) (f' := fun z => r*z^(r-1)) hderiv hnorm
    (show (1 : ℝ) ∈ Icc (1/2 : ℝ) 2 by norm_num) hx
  simpa only [Real.norm_eq_abs, Real.one_rpow] using hh

/-- Convert an error in a negative power into an error in the original
time ratio, once the negative-power ratio lies in [1/2,2]. -/
theorem inverse_power_relative_error {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ t T : ℝ, 0 < t → 0 < T →
      (t/T)^(-p) ∈ Icc (1/2 : ℝ) 2 →
      |t/T-1| ≤ C*|(t/T)^(-p)-1| := by
  obtain ⟨C, hC, hbound⟩ := rpow_relative_lipschitz (-1/p)
  refine ⟨C, hC, ?_⟩
  intro t T ht hT hratio
  have hh := hbound ((t/T)^(-p)) hratio
  rw [← Real.rpow_mul (div_pos ht hT).le,
    show (-p)*(-1/p) = (1 : ℝ) by field_simp,
    Real.rpow_one] at hh
  exact hh

theorem positive_power_relative_error {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ t T : ℝ, 0 < t → 0 < T →
      (t/T)^p ∈ Icc (1/2 : ℝ) 2 →
      |t/T-1| ≤ C*|(t/T)^p-1| := by
  obtain ⟨C, hC, hbound⟩ := rpow_relative_lipschitz (1/p)
  refine ⟨C, hC, ?_⟩
  intro t T ht hT hratio
  have hh := hbound ((t/T)^p) hratio
  rw [← Real.rpow_mul (div_pos ht hT).le,
    show p*(1/p) = (1 : ℝ) by field_simp,
    Real.rpow_one] at hh
  exact hh

end Luce.Section6
