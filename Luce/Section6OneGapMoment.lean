import Luce.Section5GapTaylor
import Luce.Section5GapMoments

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Exact survival factor retained at the starting time of the gap. -/
theorem exponentialGapMass_factor (a s h : ℝ) :
    exponentialGapMass a s h = survivalKernel s a*(1-Real.exp (-(a*h))) := by
  unfold exponentialGapMass survivalKernel
  rw [show -(s+h)*a = -s*a+ -(a*h) by ring, Real.exp_add]
  ring

theorem exponentialGapMass_le_survival {a s h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) :
    exponentialGapMass a s h ≤ a*h*survivalKernel s a := by
  rw [exponentialGapMass_factor]
  have he := Real.add_one_le_exp (-(a*h))
  have hb : 1-Real.exp (-(a*h)) ≤ a*h := by linarith
  have hc := mul_le_mul_of_nonneg_left hb (survivalKernel_pos s a).le
  simpa only [mul_comm (survivalKernel s a)] using hc

/-- The pointwise estimate used before integrating the normalized spacing.
It retains the full starting-time exponential decay for every natural moment. -/
theorem exponentialGapMass_normalized_pow_le {a W s ξ : ℝ}
    (ha : 0 < a) (hW : 0 < W) (hξ : 0 ≤ ξ) (p : ℕ) :
    0 ≤ exponentialGapMass a s (ξ/W)^p ∧
    exponentialGapMass a s (ξ/W)^p ≤ ((a/W)*survivalKernel s a)^p*ξ^p := by
  have hlen : 0 ≤ ξ/W := div_nonneg hξ hW.le
  have hmass := exponentialGapMass_nonneg (s := s) ha.le hlen
  have hh := pow_le_pow_left₀ hmass (exponentialGapMass_le_survival ha.le hlen) p
  refine ⟨pow_nonneg hmass p, ?_⟩
  have heq : a*(ξ/W)*survivalKernel s a = ((a/W)*survivalKernel s a)*ξ := by ring
  rw [heq, mul_pow] at hh
  exact hh

theorem unit_exponential_nonneg_ae : ∀ᵐ ξ ∂expMeasure 1, 0 ≤ ξ := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  apply (mem_ae_iff_prob_eq_one measurableSet_Ici).mpr
  rw [expMeasure_Ici (by norm_num : (0 : ℝ) < 1) (le_rfl : (0 : ℝ) ≤ 0)]
  simp

/-- Integrability and the factorial bound for one normalized exponential
spacing with fixed start and remaining rate. Random-start transfer is separate. -/
theorem one_gap_moment_bound {a W : ℝ} (ha : 0 < a) (hW : 0 < W)
    (s : ℝ) (p : ℕ) :
    Integrable (fun ξ => exponentialGapMass a s (ξ/W)^p) (expMeasure 1) ∧
    (∫ ξ, exponentialGapMass a s (ξ/W)^p ∂expMeasure 1) ≤
      (p.factorial : ℝ)*(a/W)^p*Real.exp (-((p : ℝ)*a*s)) := by
  let C := ((a/W)*survivalKernel s a)^p
  have hbound := (integrable_pow_expMeasure_one p).const_mul C
  have hcont : Continuous (fun ξ : ℝ => exponentialGapMass a s (ξ/W)^p) := by
    unfold exponentialGapMass survivalKernel
    fun_prop
  have hae : ∀ᵐ ξ ∂expMeasure 1,
      0 ≤ exponentialGapMass a s (ξ/W)^p ∧ exponentialGapMass a s (ξ/W)^p ≤ C*ξ^p :=
    unit_exponential_nonneg_ae.mono fun ξ hξ => exponentialGapMass_normalized_pow_le ha hW hξ p
  have hint : Integrable (fun ξ => exponentialGapMass a s (ξ/W)^p) (expMeasure 1) :=
    hbound.mono' hcont.aestronglyMeasurable (hae.mono fun ξ h => by
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2)
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ ξ, C*ξ^p ∂expMeasure 1 := integral_mono_ae hint hbound (hae.mono fun _ h => h.2)
    _ = C*(p.factorial : ℝ) := by rw [integral_const_mul, integral_pow_expMeasure_one]
    _ = _ := by
      dsimp [C, survivalKernel]
      rw [mul_pow, ← Real.exp_nat_mul]
      rw [show (p : ℝ)*(-s*a) = -((p : ℝ)*a*s) by ring]
      ring

end Luce.Section6
