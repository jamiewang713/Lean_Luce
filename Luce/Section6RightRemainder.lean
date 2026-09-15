import Luce.Section6GlobalRateUpper
import Luce.Section6EnvelopeAbsorption

noncomputable section
namespace Luce.Section6

/-- The right insertion prefactor is absorbed into a stretched-exponential
row remainder, using a polynomial rate bound derived from the profile. -/
theorem PowerProfile.right_rate_remainder {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    {d z : ℝ} (hd : 0 < d) (hz : 0 < z) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n h : ℕ) (i : Fin n), 1 ≤ h →
      ((w n).rate i*((n : ℝ)/(h : ℝ))^beta/(h : ℝ))*Real.exp (-d*(n : ℝ)^z) ≤
        C*Real.exp (-(d/2)*(n : ℝ)^z) := by
  obtain ⟨K, a, hK, ha, hrate⟩ := hp.sampled_rate_polynomial_upper
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  obtain ⟨B, hB, hb⟩ := power_envelope_absorption (a := a+beta) (p := z)
    hz.ne' (by positivity)
  refine ⟨K*(B*(1/(d/2))^((a+beta)/z)), by positivity, ?_⟩
  intro grid w hw n h i hh
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := lt_of_lt_of_le zero_lt_one hh1
  have hi := (w n).positive i
  have hscale : ((n : ℝ)/(h : ℝ))^beta ≤ (n : ℝ)^beta :=
    Real.rpow_le_rpow (by positivity) (div_le_self hn.le hh1) hbeta.le
  have hpref : (w n).rate i*((n : ℝ)/(h : ℝ))^beta/(h : ℝ) ≤ K*(n : ℝ)^(a+beta) := by
    calc
      _ ≤ (w n).rate i*((n : ℝ)/(h : ℝ))^beta := div_le_self (by positivity) hh1
      _ ≤ (K*(n : ℝ)^a)*(n : ℝ)^beta :=
        mul_le_mul (hrate grid w hw n i) hscale (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hn]; ring
  have habs : (n : ℝ)^(a+beta)*Real.exp (-d*(n : ℝ)^z) ≤
      B*(1/(d/2))^((a+beta)/z)*Real.exp (-(d/2)*(n : ℝ)^z) := by
    simpa only [neg_mul] using hb d (n : ℝ) hd hn
  calc
    _ ≤ (K*(n : ℝ)^(a+beta))*Real.exp (-d*(n : ℝ)^z) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ ≤ K*(B*(1/(d/2))^((a+beta)/z)*Real.exp (-(d/2)*(n : ℝ)^z)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left habs hK.le
    _ = _ := by ring

end Luce.Section6
