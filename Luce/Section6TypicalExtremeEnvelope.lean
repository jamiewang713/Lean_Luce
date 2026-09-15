import Luce.Section6ExceptionalRestrictedSums
import Luce.Section6EnvelopeAbsorption

noncomputable section
namespace Luce.Section6

/-- The typical comparison kernel restricted to the extreme region. The
third depth is the physical full-rank denominator: h on the right and a
after exchanging numerator/denominator depths on the left. -/
def extremeTypicalEnvelope (b v d : ℝ) (a h s : ℕ) : ℝ :=
  if ((a : ℝ)/(h : ℝ))^b ≤ (min (a : ℝ) (h : ℝ))^v then 0
  else (((a : ℝ)/(h : ℝ))^b/(s : ℝ))*Real.exp (-d*((a : ℝ)/(h : ℝ))^b)

theorem extremeTypicalEnvelope_nonneg (b v d : ℝ) (a h s : ℕ) :
    0 ≤ extremeTypicalEnvelope b v d a h s := by
  unfold extremeTypicalEnvelope
  split_ifs <;> positivity

/-- Polynomial absorption on the extreme set yields a summable exceptional
majorant, uniformly in either choice of physical denominator. -/
theorem extremeTypicalEnvelope_le_exceptional {b v d : ℝ}
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ a h s : ℕ, 1 ≤ a → 1 ≤ h → 1 ≤ s →
      extremeTypicalEnvelope b v d a h s ≤
        C*exceptionalEnvelope b v (d/2) (b*v/(b+v)) a h := by
  have hk : 0 < b*v/(b+v) := div_pos (mul_pos hb hv) (add_pos hb hv)
  obtain ⟨C, hC, habs⟩ := power_envelope_absorption (a := b) hk.ne' (div_nonneg hb.le hk.le)
  refine ⟨C*(1/(d/2))^(b/(b*v/(b+v))), by positivity, ?_⟩
  intro a h s ha hh hs
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have ha0 : (0 : ℝ) < a := zero_lt_one.trans_le haR
  unfold extremeTypicalEnvelope exceptionalEnvelope
  split_ifs with hext
  · simp
  · have hx := (extreme_ratio_bounds haR hhR hb hv hext).2.2.le
    have hz := ratio_power_over_depth_le ha0.le hhR hsR hb.le
    have he : Real.exp (-d*((a : ℝ)/(h : ℝ))^b) ≤
        Real.exp (-d*(a : ℝ)^(b*v/(b+v))) := Real.exp_le_exp.mpr (by nlinarith)
    have hm := mul_le_mul hz he (Real.exp_pos _).le (Real.rpow_nonneg ha0.le b)
    apply hm.trans
    simpa only [neg_mul] using habs d (a : ℝ) hd ha0

end Luce.Section6
