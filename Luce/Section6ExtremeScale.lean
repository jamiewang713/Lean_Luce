import Luce.Section6RateTimeLower

noncomputable section
namespace Luce.Section6

theorem right_extreme_exponent_bounds {beta : ℝ} (hb : 0 < beta) :
    0 < beta/(beta+1) ∧ beta/(beta+1) < 1 := by
  constructor
  · exact div_pos hb (by linarith)
  · apply (div_lt_one (by linarith)).mpr
    linarith

/-- The different right time scale balances the marked survival exponent
with the comparison survivor depth. -/
theorem right_extreme_scale_identity {a beta : ℝ} (ha : 0 < a) (hb : 0 < beta) :
    (a/(a^(beta/(beta+1))))^beta = a^(beta/(beta+1)) := by
  rw [Real.div_rpow ha.le (Real.rpow_nonneg ha.le _), ← Real.rpow_mul ha.le,
    ← Real.rpow_sub ha]
  congr 1
  field_simp [ne_of_gt (show 0 < beta+1 by linarith)]
  ring

theorem right_extreme_depth_le {a beta : ℝ} (ha : 1 ≤ a) (hb : 0 < beta) :
    a^(beta/(beta+1)) ≤ a := by
  calc
    _ ≤ a^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha (right_extreme_exponent_bounds hb).2.le
    _ = a := Real.rpow_one a

theorem right_extreme_depth_cutoff {H beta : ℝ} (hH : 0 < H) (hb : 0 < beta) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, A ≤ a → 1 ≤ a ∧ H ≤ a^(beta/(beta+1)) := by
  have hz := (right_extreme_exponent_bounds hb).1
  refine ⟨max 1 (H^((beta/(beta+1))⁻¹)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro a ha
  refine ⟨(le_max_left _ _).trans ha, ?_⟩
  have he : (H^((beta/(beta+1))⁻¹))^(beta/(beta+1)) = H := by
    rw [← Real.rpow_mul hH.le, inv_mul_cancel₀ hz.ne', Real.rpow_one]
  rw [← he]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hH.le _) ((le_max_right _ _).trans ha) hz.le

end Luce.Section6
