import Luce.Section6ExceptionalSummability

noncomputable section
namespace Luce.Section6

/-- The manuscript's sum of restricted row and column suprema, written
literally for a deterministic comparison kernel. -/
def restrictedKernelSums (F : ℕ → ℕ → ℝ) (A : ℕ) : ℝ :=
  sSup {z : ℝ | ∃ a : ℕ, A ≤ a ∧ z = ∑' h : ℕ, if A ≤ h then F a h else 0} +
  sSup {z : ℝ | ∃ h : ℕ, A ≤ h ∧ z = ∑' a : ℕ, if A ≤ a then F a h else 0}

theorem restrictedKernelSums_transpose (F : ℕ → ℕ → ℝ) (A : ℕ) :
    restrictedKernelSums (fun a h => F h a) A = restrictedKernelSums F A := by
  unfold restrictedKernelSums
  exact add_comm _ _

/-- Transfer the proved exceptional-kernel tails through a pointwise
majorant. Concrete typical-kernel theorems construct this majorant. -/
theorem restrictedKernelSums_of_exceptional_domination {b v d nu C : ℝ}
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d) (hnu : 0 < nu) (hC : 0 < C)
    (F : ℕ → ℕ → ℝ) (hF : ∀ a h, 0 ≤ F a h)
    (hdom : ∀ a h : ℕ, 1 ≤ a → 1 ≤ h → F a h ≤ C*exceptionalEnvelope b v d nu a h) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℕ, 1 ≤ A →
      restrictedKernelSums F A ≤ K*Real.exp (-(d/2)*(A : ℝ)^nu) := by
  obtain ⟨Cr, hCr, hr⟩ := exceptionalEnvelope_row_tail hb hv hd hnu
  obtain ⟨Cc, hCc, hc⟩ := exceptionalEnvelope_column_tail (b := b) (v := v) hd hnu
  refine ⟨C*(Cr+Cc), mul_pos hC (add_pos hCr hCc), ?_⟩
  intro A hA
  have hrow (a : ℕ) (ha : A ≤ a) :
      (∑' h : ℕ, if A ≤ h then F a h else 0) ≤ C*Cr*Real.exp (-(d/2)*(A : ℝ)^nu) := by
    have ht := tsum_le_scaled_of_nonneg
      (F := fun h : ℕ => if A ≤ h then F a h else 0)
      (G := fun h : ℕ => if A ≤ h then exceptionalEnvelope b v d nu a h else 0)
      (fun h => by split_ifs <;> simp only [le_refl, hF])
      (fun h => by
        split_ifs with hh
        · exact hdom a h (hA.trans ha) (hA.trans hh)
        · simp)
      (exceptionalEnvelope_row_summable hb hv hA ha)
    have hbnd := mul_le_mul_of_nonneg_left (hr A a hA ha) hC.le
    nlinarith only [ht, hbnd]
  have hcol (h : ℕ) (hh : A ≤ h) :
      (∑' a : ℕ, if A ≤ a then F a h else 0) ≤ C*Cc*Real.exp (-(d/2)*(A : ℝ)^nu) := by
    have ht := tsum_le_scaled_of_nonneg
      (F := fun a : ℕ => if A ≤ a then F a h else 0)
      (G := fun a : ℕ => if A ≤ a then exceptionalEnvelope b v d nu a h else 0)
      (fun a => by split_ifs <;> simp only [le_refl, hF])
      (fun a => by
        split_ifs with ha
        · exact hdom a h (hA.trans ha) (hA.trans hh)
        · simp)
      (exceptionalEnvelope_column_summable hd hnu A h)
    have hbnd := mul_le_mul_of_nonneg_left (hc A h) hC.le
    nlinarith only [ht, hbnd]
  have hrSup : sSup {z : ℝ | ∃ a : ℕ, A ≤ a ∧ z = ∑' h : ℕ, if A ≤ h then F a h else 0} ≤
      C*Cr*Real.exp (-(d/2)*(A : ℝ)^nu) := by
    apply csSup_le
    · exact ⟨_, A, le_refl A, rfl⟩
    · rintro z ⟨a, ha, rfl⟩
      exact hrow a ha
  have hcSup : sSup {z : ℝ | ∃ h : ℕ, A ≤ h ∧ z = ∑' a : ℕ, if A ≤ a then F a h else 0} ≤
      C*Cc*Real.exp (-(d/2)*(A : ℝ)^nu) := by
    apply csSup_le
    · exact ⟨_, A, le_refl A, rfl⟩
    · rintro z ⟨h, hh, rfl⟩
      exact hcol h hh
  unfold restrictedKernelSums
  nlinarith only [hrSup, hcSup]

end Luce.Section6
