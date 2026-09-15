import Luce.Section6WeightedIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

theorem exists_power_exp_bound {a : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → x^a*Real.exp (-x) ≤ C := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a 1 zero_lt_one
  have he : ∀ᶠ x : ℝ in atTop, x^a*Real.exp (-x) ≤ 1 := by
    have hh := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hh] with x hx
    simpa using hx.le
  obtain ⟨R, hR⟩ := eventually_atTop.mp he
  let T := max R 1
  have hT : (0 : ℝ) ≤ T := zero_le_one.trans (le_max_right _ _)
  have hcont : Continuous (fun x : ℝ => x^a*Real.exp (-x)) :=
    (Real.continuous_rpow_const ha).mul (Real.continuous_exp.comp continuous_neg)
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) hcont.continuousOn
  refine ⟨max (v^a*Real.exp (-v)) 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro x hx
  by_cases hxT : x ≤ T
  · exact (hmax ⟨hx, hxT⟩).trans (le_max_left _ _)
  · exact (hR x ((le_max_left _ _).trans (le_of_not_ge hxT))).trans (le_max_right _ _)

/-- Polynomial factors can be absorbed into half the exponential decay.
The constant is independent of the scaling parameter r and the point s. -/
theorem power_envelope_absorption {a p : ℝ} (hp : p ≠ 0) (ha : 0 ≤ a/p) :
    ∃ C : ℝ, 0 < C ∧ ∀ r s : ℝ, 0 < r → 0 < s →
      s^a*Real.exp (-(r*s^p)) ≤
        C*(1/(r/2))^(a/p)*Real.exp (-((r/2)*s^p)) := by
  obtain ⟨C, hC, hbound⟩ := exists_power_exp_bound ha
  refine ⟨C, hC, ?_⟩
  intro r s hr hs
  have hu : 0 < (r/2)*s^p := mul_pos (half_pos hr) (Real.rpow_pos_of_pos hs _)
  have hpower : ((r/2)*s^p)^(a/p) = (r/2)^(a/p)*s^a := by
    rw [Real.mul_rpow (half_pos hr).le (Real.rpow_pos_of_pos hs p).le,
      ← Real.rpow_mul hs.le]
    have he : p*(a/p) = a := by field_simp
    rw [he]
  have hb := hbound ((r/2)*s^p) hu.le
  rw [hpower] at hb
  have hp0 : 0 < (r/2)^(a/p) := Real.rpow_pos_of_pos (half_pos hr) _
  have hb' : s^a*Real.exp (-((r/2)*s^p)) ≤ C/(r/2)^(a/p) := by
    apply (le_div_iff₀ hp0).mpr
    nlinarith [hb]
  have he : Real.exp (-(r*s^p)) =
      Real.exp (-((r/2)*s^p))*Real.exp (-((r/2)*s^p)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, ← mul_assoc]
  calc
    _ ≤ (C/(r/2)^(a/p))*Real.exp (-((r/2)*s^p)) :=
      mul_le_mul_of_nonneg_right hb' (Real.exp_pos _).le
    _ = _ := by rw [Real.div_rpow zero_le_one (half_pos hr).le, Real.one_rpow]; ring

end Luce.Section6
