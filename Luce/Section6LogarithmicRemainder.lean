import Luce.Section6GlobalRateUpper
import Luce.Section6EnvelopeAbsorption

noncomputable section
namespace Luce.Section6

/-- Absorption preserves the manuscript's full sqrt(n*h) exponent. The
polynomial rate bound is proved from the sampled profile, not assumed. -/
theorem PowerProfile.logarithmic_rate_remainder {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n h : ℕ) (i : Fin n), 1 ≤ h →
      ((w n).rate i/(h : ℝ))*Real.exp (-d*Real.sqrt ((n : ℝ)*(h : ℝ))) ≤
        C*Real.exp (-(d/2)*Real.sqrt ((n : ℝ)*(h : ℝ))) := by
  obtain ⟨K, a, hK, ha, hrate⟩ := hp.sampled_rate_polynomial_upper
  obtain ⟨B, hB, hb⟩ := power_envelope_absorption (a := 2*a) (p := 1)
    one_ne_zero (by positivity)
  refine ⟨K*(B*(1/(d/2))^(2*a)), by positivity, ?_⟩
  intro grid w hw n h i hh
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := lt_of_lt_of_le zero_lt_one hh1
  have hi := (w n).positive i
  let s := Real.sqrt ((n : ℝ)*(h : ℝ))
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos hn hh0)
  have hsq : s^2 = (n : ℝ)*(h : ℝ) := Real.sq_sqrt (by positivity)
  have hns : (n : ℝ) ≤ s^2 := by rw [hsq]; nlinarith
  have hscale : (n : ℝ)^a ≤ s^(2*a) := by
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast_mul hs.le]
    exact Real.rpow_le_rpow hn.le hns ha
  have hpref : (w n).rate i/(h : ℝ) ≤ K*s^(2*a) :=
    (div_le_self hi.le hh1).trans ((hrate grid w hw n i).trans
      (mul_le_mul_of_nonneg_left hscale hK.le))
  have habs : s^(2*a)*Real.exp (-d*s) ≤
      B*(1/(d/2))^(2*a)*Real.exp (-(d/2)*s) := by
    simpa only [div_one, Real.rpow_one, neg_mul] using hb d s hd hs
  calc
    _ ≤ (K*s^(2*a))*Real.exp (-d*s) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ ≤ K*(B*(1/(d/2))^(2*a)*Real.exp (-(d/2)*s)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left habs hK.le
    _ = _ := by ring

end Luce.Section6
