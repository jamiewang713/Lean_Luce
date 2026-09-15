import Luce.Section6ExceptionalSums

noncomputable section
namespace Luce.Section6

/-- The literal sum of the two restricted suprema for the right exceptional
kernel. The left exceptional kernel is the transpose, so the two suprema
exchange roles. No assumed summability or uniform bound is an input. -/
theorem exceptionalEnvelope_restricted_sums {b v d nu : ℝ} (hb : 0 < b) (hv : 0 < v)
    (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ, 1 ≤ A →
      sSup {z : ℝ | ∃ a : ℕ, A ≤ a ∧ z =
        ∑' h : ℕ, if A ≤ h then exceptionalEnvelope b v d nu a h else 0} +
      sSup {z : ℝ | ∃ h : ℕ, A ≤ h ∧ z =
        ∑' a : ℕ, if A ≤ a then exceptionalEnvelope b v d nu a h else 0} ≤
        C*Real.exp (-(d/2)*(A : ℝ)^nu) := by
  obtain ⟨Cr, hCr, hr⟩ := exceptionalEnvelope_row_tail hb hv hd hnu
  obtain ⟨Cc, hCc, hc⟩ := exceptionalEnvelope_column_tail (b := b) (v := v) hd hnu
  refine ⟨Cr+Cc, add_pos hCr hCc, ?_⟩
  intro A hA
  have hrow : sSup {z : ℝ | ∃ a : ℕ, A ≤ a ∧ z =
      ∑' h : ℕ, if A ≤ h then exceptionalEnvelope b v d nu a h else 0} ≤
      Cr*Real.exp (-(d/2)*(A : ℝ)^nu) := by
    apply csSup_le
    · exact ⟨_, A, le_refl A, rfl⟩
    · rintro z ⟨a, ha, rfl⟩
      exact hr A a hA ha
  have hcol : sSup {z : ℝ | ∃ h : ℕ, A ≤ h ∧ z =
      ∑' a : ℕ, if A ≤ a then exceptionalEnvelope b v d nu a h else 0} ≤
      Cc*Real.exp (-(d/2)*(A : ℝ)^nu) := by
    apply csSup_le
    · exact ⟨_, A, le_refl A, rfl⟩
    · rintro z ⟨h, hh, rfl⟩
      exact hc A h
  nlinarith only [hrow, hcol]

/-- The left exceptional envelope is exactly the transpose, with decay in
the full-rank depth h. Its restricted suprema satisfy the same estimate. -/
theorem exceptionalEnvelope_transpose_restricted_sums {b v d nu : ℝ}
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ, 1 ≤ A →
      sSup {z : ℝ | ∃ a : ℕ, A ≤ a ∧ z =
        ∑' h : ℕ, if A ≤ h then exceptionalEnvelope b v d nu h a else 0} +
      sSup {z : ℝ | ∃ h : ℕ, A ≤ h ∧ z =
        ∑' a : ℕ, if A ≤ a then exceptionalEnvelope b v d nu h a else 0} ≤
        C*Real.exp (-(d/2)*(A : ℝ)^nu) := by
  obtain ⟨C, hC, hs⟩ := exceptionalEnvelope_restricted_sums hb hv hd hnu
  refine ⟨C, hC, ?_⟩
  intro A hA
  simpa only [add_comm] using hs A hA

end Luce.Section6
