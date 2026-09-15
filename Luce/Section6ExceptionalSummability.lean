import Luce.Section6ExceptionalSums

noncomputable section
namespace Luce.Section6

theorem exceptionalEnvelope_row_summable {b v d nu : ℝ} (hb : 0 < b) (hv : 0 < v)
    {A a : ℕ} (hA : 1 ≤ A) (ha : A ≤ a) :
    Summable (fun h : ℕ => if A ≤ h then exceptionalEnvelope b v d nu a h else 0) := by
  apply summable_of_ne_finset_zero (s := Finset.range a)
  intro h hh
  split_ifs with hAh
  · by_contra he
    exact hh (Finset.mem_range.mpr (exceptionalEnvelope_support hb hv (hA.trans ha) (hA.trans hAh) he))
  · rfl

theorem exceptionalEnvelope_column_summable {b v d nu : ℝ} (hd : 0 < d) (hnu : 0 < nu)
    (A h : ℕ) :
    Summable (fun a : ℕ => if A ≤ a then exceptionalEnvelope b v d nu a h else 0) := by
  have hs : Summable (fun a : ℕ => Real.exp (-d*(a : ℝ)^nu)) := by
    simpa using summable_weighted_stretched_exp (b := 0) (by norm_num) hd hnu
  apply Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) hs
  · split_ifs <;> simp only [le_refl, exceptionalEnvelope_nonneg]
  · split_ifs
    · exact exceptionalEnvelope_le_exp _ _ _ _ _ _
    · positivity

/-- A generic nonnegative-series comparison. All summability premises are
discharged by the actual exceptional kernels in the restricted-sum transfer. -/
theorem tsum_le_scaled_of_nonneg {F G : ℕ → ℝ} {C : ℝ}
    (hF : ∀ n, 0 ≤ F n) (hdom : ∀ n, F n ≤ C*G n) (hG : Summable G) :
    (∑' n, F n) ≤ C*(∑' n, G n) := by
  have hs := hG.mul_left C
  have hf := Summable.of_nonneg_of_le hF hdom hs
  simpa only [tsum_mul_left] using hf.tsum_le_tsum hdom hs

end Luce.Section6
