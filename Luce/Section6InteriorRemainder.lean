import Luce.Section6GlobalRateUpper
import Luce.Section6EnvelopeAbsorption

noncomputable section
namespace Luce.Section6

/-- The middle-rank exponential remainder is uniform over all source labels.
The polynomial rate bound is discharged from the original sampled profile. -/
theorem PowerProfile.interior_rate_remainder {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n),
      ((w n).rate i/(n : ℝ))*Real.exp (-d*(n : ℝ)) ≤
        C*Real.exp (-(d/2)*(n : ℝ)) := by
  obtain ⟨K, a, hK, ha, hrate⟩ := hp.sampled_rate_polynomial_upper
  obtain ⟨B, hB, hb⟩ := power_envelope_absorption (a := a) (p := 1)
    one_ne_zero (by simpa using ha)
  refine ⟨K*(B*(1/(d/2))^a), by positivity, ?_⟩
  intro grid w hw n i
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hi := (w n).positive i
  have hdiv : (w n).rate i/(n : ℝ) ≤ (w n).rate i :=
    div_le_self hi.le hn1
  have hh : (n : ℝ)^a*Real.exp (-d*(n : ℝ)) ≤
      B*(1/(d/2))^a*Real.exp (-(d/2)*(n : ℝ)) := by
    simpa only [div_one, Real.rpow_one, neg_mul] using hb d (n : ℝ) hd hn
  calc
    _ ≤ (K*(n : ℝ)^a)*Real.exp (-d*(n : ℝ)) :=
      mul_le_mul_of_nonneg_right (hdiv.trans (hrate grid w hw n i)) (Real.exp_pos _).le
    _ ≤ K*(B*(1/(d/2))^a*Real.exp (-(d/2)*(n : ℝ))) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hK.le
    _ = _ := by ring

end Luce.Section6
