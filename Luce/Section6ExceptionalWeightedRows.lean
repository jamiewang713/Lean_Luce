import Luce.Section6ExceptionalSummability

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The right exceptional support has target depth smaller than source
depth, so every nonnegative manuscript weight is at most one there. -/
theorem exceptional_weighted_factor_le {b v d nu kappa : ℝ}
    (hb : 0 < b) (hv : 0 < v) (hk : 0 ≤ kappa)
    {a h : ℕ} (ha : 1 ≤ a) (hh : 1 ≤ h) :
    ((h : ℝ)/(a : ℝ))^kappa*exceptionalEnvelope b v d nu a h ≤
      exceptionalEnvelope b v d nu a h := by
  by_cases he : exceptionalEnvelope b v d nu a h = 0
  · simp only [he, mul_zero, le_refl]
  have hha := exceptionalEnvelope_support hb hv ha hh he
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hratio : (h : ℝ)/(a : ℝ) ≤ 1 := by
    apply (div_le_one haR).mpr
    exact_mod_cast hha.le
  have hpow := Real.rpow_le_one (by positivity : 0 ≤ (h : ℝ)/(a : ℝ)) hratio hk
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow (exceptionalEnvelope_nonneg _ _ _ _ _ _)

theorem right_exceptional_weighted_row_bound {b v d nu kappa : ℝ}
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d) (hnu : 0 < nu) (hk : 0 ≤ kappa) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ, 1 ≤ a → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/(a : ℝ))^kappa*
      exceptionalEnvelope b v d nu a h) ≤ C := by
  obtain ⟨C, hC, ht⟩ := exceptionalEnvelope_row_tail hb hv hd hnu
  refine ⟨C, hC, ?_⟩
  intro a ha M
  have hs := exceptionalEnvelope_row_summable (d := d) (nu := nu) hb hv (a := a) (A := 1) le_rfl ha
  calc
    _ ≤ ∑ h ∈ Finset.Ico 1 (M+1), if 1 ≤ h then exceptionalEnvelope b v d nu a h else 0 := by
      apply Finset.sum_le_sum
      intro h hh
      have hh1 := (Finset.mem_Ico.mp hh).1
      rw [if_pos hh1]
      exact exceptional_weighted_factor_le hb hv hk ha hh1
    _ ≤ ∑' h : ℕ, if 1 ≤ h then exceptionalEnvelope b v d nu a h else 0 :=
      hs.sum_le_tsum _ (fun h _ => by split_ifs <;> simp only [le_refl, exceptionalEnvelope_nonneg])
    _ ≤ C*Real.exp (-(d/2)*(1 : ℕ)^nu) := ht 1 a le_rfl ha
    _ ≤ C := by
      have he : Real.exp (-(d/2)*(1 : ℕ)^nu) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (half_pos hd).le) (by positivity))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he hC.le

/-- The left envelope is the transpose; its weight is likewise at most
one on its exceptional support. -/
theorem left_exceptional_weighted_row_bound {b v d nu kappa : ℝ}
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d) (hnu : 0 < nu) (hk : 0 ≤ kappa) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ, 1 ≤ a → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), ((a : ℝ)/(h : ℝ))^kappa*
      exceptionalEnvelope b v d nu h a) ≤ C := by
  obtain ⟨C, hC, ht⟩ := exceptionalEnvelope_column_tail (b := b) (v := v) hd hnu
  refine ⟨C, hC, ?_⟩
  intro a ha M
  have hs := exceptionalEnvelope_column_summable (b := b) (v := v) hd hnu 1 a
  calc
    _ ≤ ∑ h ∈ Finset.Ico 1 (M+1), if 1 ≤ h then exceptionalEnvelope b v d nu h a else 0 := by
      apply Finset.sum_le_sum
      intro h hh
      have hh1 := (Finset.mem_Ico.mp hh).1
      rw [if_pos hh1]
      exact exceptional_weighted_factor_le hb hv hk hh1 ha
    _ ≤ ∑' h : ℕ, if 1 ≤ h then exceptionalEnvelope b v d nu h a else 0 :=
      hs.sum_le_tsum _ (fun h _ => by split_ifs <;> simp only [le_refl, exceptionalEnvelope_nonneg])
    _ ≤ C*Real.exp (-(d/2)*(1 : ℕ)^nu) := ht 1 a
    _ ≤ C := by
      have he : Real.exp (-(d/2)*(1 : ℕ)^nu) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (half_pos hd).le) (by positivity))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he hC.le

end Luce.Section6
