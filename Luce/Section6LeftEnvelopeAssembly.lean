import Luce.Section6DominationMatrixCornerEnvelope
import Luce.Section6DominationMatrixFixedLeftRate

noncomputable section
namespace Luce.Section6

/-- The left corner envelope and exact fixed-target rate estimate share
one constant and an integer cutoff. Both estimates cover every row size. -/
theorem PowerProfile.domination_matrix_left_envelope_assembly {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p : ℕ) (hp1 : 0 < p)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    ∃ (H : ℕ) (C d nu delta : ℝ), 1 ≤ H ∧ 0 < C ∧ 0 < d ∧ 0 < nu ∧
      0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i j : Fin n),
      (H ≤ j.val+1 → ((j.val : ℝ)+1)/(n : ℝ) ≤ delta →
        ((i.val : ℝ)+1)/(n : ℝ) ≤ delta →
        insertionDominationMatrix (w n) r p i j ≤
          C*(((((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha/((j.val : ℝ)+1))*
            Real.exp (-d*(((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha)+
            exceptionalEnvelope alpha v d nu (j.val+1) (i.val+1))) ∧
      (j.val+1 ≤ H → insertionDominationMatrix (w n) r p i j ≤
        C*((w n).rate i/(n : ℝ)^alpha)) := by
  obtain ⟨B, d, nu, h, delta, hB, hd, hnu, hh, hdelta, hdelta1, henv⟩ :=
    hp.domination_matrix_left_corner_envelope r p hp1 v hv hv1
  let H := max 1 ⌈h⌉₊
  obtain ⟨F, hF, hfixed⟩ := hp.domination_matrix_fixed_left_rate r H p hp1
  refine ⟨H, B+F, d, nu, delta, le_max_left _ _, add_pos hB hF, hd, hnu,
    hdelta, hdelta1, ?_⟩
  intro grid w hw n i j
  constructor
  · intro hH hj hi
    have hle : h ≤ (j.val : ℝ)+1 := by
      apply (Nat.le_ceil h).trans
      exact_mod_cast ((le_max_right 1 ⌈h⌉₊).trans hH)
    apply (henv grid w hw n i j hle hj hi).trans
    apply mul_le_mul_of_nonneg_right (by linarith)
    have := exceptionalEnvelope_nonneg alpha v d nu (j.val+1) (i.val+1)
    positivity
  · intro hH
    apply (hfixed grid w hw n i j hH).trans
    apply mul_le_mul_of_nonneg_right (by linarith)
    exact div_nonneg ((w n).positive i).le (Real.rpow_nonneg (Nat.cast_nonneg n) alpha)

end Luce.Section6
