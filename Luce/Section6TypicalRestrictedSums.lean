import Luce.Section6RestrictedSumDomination
import Luce.Section6TypicalExtremeEnvelope

noncomputable section
namespace Luce.Section6

/-- The right typical kernel, restricted to the complement of the moderate
set, has the manuscript's stretched-exponential restricted sum bound. -/
theorem right_typical_extreme_restricted_sums {b v d : ℝ}
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ, 1 ≤ A →
      restrictedKernelSums (fun a h => extremeTypicalEnvelope b v d a h h) A ≤
        C*Real.exp (-(d/4)*(A : ℝ)^(b*v/(b+v))) := by
  obtain ⟨C, hC, hdom⟩ := extremeTypicalEnvelope_le_exceptional hb hv hd
  have hk : 0 < b*v/(b+v) := div_pos (mul_pos hb hv) (add_pos hb hv)
  obtain ⟨K, hK, htail⟩ := restrictedKernelSums_of_exceptional_domination hb hv (half_pos hd) hk hC
    (fun a h => extremeTypicalEnvelope b v d a h h)
    (fun a h => extremeTypicalEnvelope_nonneg _ _ _ _ _ _)
    (fun a h ha hh => hdom a h h ha hh hh)
  refine ⟨K, hK, ?_⟩
  intro A hA
  simpa only [show d/2/2 = d/4 by ring] using htail A hA

/-- The left typical kernel has physical denominator h even after its
power ratio is reversed. The domination is proved with that denominator
before the restricted suprema are transposed. -/
theorem left_typical_extreme_restricted_sums {b v d : ℝ}
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ, 1 ≤ A →
      restrictedKernelSums (fun a h => extremeTypicalEnvelope b v d h a h) A ≤
        C*Real.exp (-(d/4)*(A : ℝ)^(b*v/(b+v))) := by
  obtain ⟨C, hC, hdom⟩ := extremeTypicalEnvelope_le_exceptional hb hv hd
  have hk : 0 < b*v/(b+v) := div_pos (mul_pos hb hv) (add_pos hb hv)
  obtain ⟨K, hK, htail⟩ := restrictedKernelSums_of_exceptional_domination hb hv (half_pos hd) hk hC
    (fun a h => extremeTypicalEnvelope b v d a h a)
    (fun a h => extremeTypicalEnvelope_nonneg _ _ _ _ _ _)
    (fun a h ha hh => hdom a h a ha hh ha)
  refine ⟨K, hK, ?_⟩
  intro A hA
  rw [show (fun a h => extremeTypicalEnvelope b v d h a h) =
    (fun a h => (fun a h => extremeTypicalEnvelope b v d a h a) h a) from rfl,
    restrictedKernelSums_transpose]
  simpa only [show d/2/2 = d/4 by ring] using htail A hA

end Luce.Section6
