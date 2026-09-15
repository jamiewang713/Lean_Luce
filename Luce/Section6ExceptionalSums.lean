import Luce.Section6StretchedExponentialSums
import Luce.Section6ExtremeRatios

noncomputable section
namespace Luce.Section6

/-- Literal right exceptional envelope; the left envelope is its transpose.
These deterministic comparison kernels do not redefine insertion probabilities. -/
def exceptionalEnvelope (b v d nu : ℝ) (a h : ℕ) : ℝ :=
  if ((a : ℝ)/(h : ℝ))^b ≤ (min (a : ℝ) (h : ℝ))^v then 0
  else Real.exp (-d*(a : ℝ)^nu)

theorem exceptionalEnvelope_nonneg (b v d nu : ℝ) (a h : ℕ) :
    0 ≤ exceptionalEnvelope b v d nu a h := by
  unfold exceptionalEnvelope
  split_ifs <;> positivity

theorem exceptionalEnvelope_le_exp (b v d nu : ℝ) (a h : ℕ) :
    exceptionalEnvelope b v d nu a h ≤ Real.exp (-d*(a : ℝ)^nu) := by
  unfold exceptionalEnvelope
  split_ifs
  · positivity
  · exact le_rfl

theorem exceptionalEnvelope_support {b v d nu : ℝ} (hb : 0 < b) (hv : 0 < v)
    {a h : ℕ} (ha : 1 ≤ a) (hh : 1 ≤ h) (he : exceptionalEnvelope b v d nu a h ≠ 0) :
    h < a := by
  have hext : ¬ ((a : ℝ)/(h : ℝ))^b ≤ (min (a : ℝ) (h : ℝ))^v := by
    intro ht
    exact he (if_pos ht)
  exact_mod_cast (extreme_ratio_bounds (by exact_mod_cast ha) (by exact_mod_cast hh) hb hv hext).1

theorem exceptionalEnvelope_column_tail {b v d nu : ℝ} (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ A h : ℕ,
      (∑' a : ℕ, if A ≤ a then exceptionalEnvelope b v d nu a h else 0) ≤
        C*Real.exp (-(d/2)*(A : ℝ)^nu) := by
  obtain ⟨C, hC, htail⟩ := weighted_stretched_exp_tail (b := 0) (by norm_num) hd hnu
  refine ⟨C, hC, ?_⟩
  intro A h
  have hs : Summable (fun a : ℕ => Real.exp (-d*(a : ℝ)^nu)) := by
    simpa using summable_weighted_stretched_exp (b := 0) (by norm_num) hd hnu
  have ht : Summable (fun a : ℕ => if A ≤ a then Real.exp (-d*(a : ℝ)^nu) else 0) :=
    by
      apply (hs.indicator {a | A ≤ a}).congr
      intro a
      simp [Set.indicator_apply]
  have hpoint (a : ℕ) : (if A ≤ a then exceptionalEnvelope b v d nu a h else 0) ≤
      (if A ≤ a then Real.exp (-d*(a : ℝ)^nu) else 0) := by
    split_ifs <;> simp only [le_refl, exceptionalEnvelope_le_exp]
  have hn (a : ℕ) : 0 ≤ (if A ≤ a then exceptionalEnvelope b v d nu a h else 0) := by
    split_ifs <;> simp only [le_refl, exceptionalEnvelope_nonneg]
  have hf := Summable.of_nonneg_of_le hn hpoint ht
  exact (hf.tsum_le_tsum hpoint ht).trans (by simpa using htail A)

theorem exceptionalEnvelope_row_tail {b v d nu : ℝ} (hb : 0 < b) (hv : 0 < v)
    (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ A a : ℕ, 1 ≤ A → A ≤ a →
      (∑' h : ℕ, if A ≤ h then exceptionalEnvelope b v d nu a h else 0) ≤
        C*Real.exp (-(d/2)*(A : ℝ)^nu) := by
  obtain ⟨C, hC, htail⟩ := weighted_stretched_exp_tail (b := 1) (by norm_num) hd hnu
  refine ⟨C, hC, ?_⟩
  intro A a hA hAa
  have hzero (h : ℕ) (hh : h ∉ Finset.range a) :
      (if A ≤ h then exceptionalEnvelope b v d nu a h else 0) = 0 := by
    split_ifs with hAh
    · by_contra he
      exact hh (Finset.mem_range.mpr (exceptionalEnvelope_support hb hv (hA.trans hAa) (hA.trans hAh) he))
    · rfl
  rw [tsum_eq_sum hzero]
  have hfinite : (∑ h ∈ Finset.range a, if A ≤ h then exceptionalEnvelope b v d nu a h else 0) ≤
      (a : ℝ)*Real.exp (-d*(a : ℝ)^nu) := by
    calc
      _ ≤ ∑ _h ∈ Finset.range a, Real.exp (-d*(a : ℝ)^nu) := by
        apply Finset.sum_le_sum
        intro h _
        split_ifs
        · exact exceptionalEnvelope_le_exp _ _ _ _ _ _
        · positivity
      _ = _ := by simp
  have hs : Summable (fun n : ℕ => (n : ℝ)*Real.exp (-d*(n : ℝ)^nu)) := by
    simpa using summable_weighted_stretched_exp (b := 1) (by norm_num) hd hnu
  have ht : Summable (fun n : ℕ => if A ≤ n then (n : ℝ)*Real.exp (-d*(n : ℝ)^nu) else 0) :=
    by
      apply (hs.indicator {n | A ≤ n}).congr
      intro n
      simp [Set.indicator_apply]
  have hsingle := ht.le_tsum a (fun n _ => by split_ifs <;> positivity)
  rw [if_pos hAa] at hsingle
  exact hfinite.trans (hsingle.trans (by simpa using htail A))

end Luce.Section6
