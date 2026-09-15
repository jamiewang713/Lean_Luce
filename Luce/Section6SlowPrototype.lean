import Luce.Section6MonotoneQuadrature
import Luce.Section6PowerIntegrals

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem slow_survival_antitone {beta r : ℝ} (hb : 0 ≤ beta) (hr : 0 ≤ r) :
    AntitoneOn (fun s : ℝ => Real.exp (-(r*s^beta))) (Ici 0) := by
  intro x hx y hy hxy
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy hb) hr)

theorem slow_survival_quadrature (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {beta r : ℝ} (hb : 0 < beta) (hr : 0 ≤ r) :
    |(∑ i : Fin n, Real.exp (-(r*(samplePoint grid n i)^beta)))/(n : ℝ) -
      ∫ s in (0 : ℝ)..1, Real.exp (-(r*s^beta))| ≤ 1/(n : ℝ) := by
  have h := antitone_sample_average_error grid hn
    ((slow_survival_antitone hb.le hr).mono Icc_subset_Ici_self)
  simp only [Real.zero_rpow hb.ne', mul_zero, neg_zero, Real.exp_zero, Real.one_rpow, mul_one] at h
  exact h.trans (div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) (Nat.cast_nonneg n))

theorem slow_survival_tail_bound {beta r : ℝ} (hb : 0 < beta) (hr : 0 < r) :
    (∫ s in Ioi (1 : ℝ), Real.exp (-(r*s^beta))) ≤
      Real.exp (-r/2) * ((1/(r/2))^(1/beta) * Real.Gamma (1+1/beta)) := by
  have hfull := integrableOn_slow_survival hb hr
  have hhalf := integrableOn_slow_survival hb (half_pos hr)
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  have he : ∀ s ∈ Ioi (1 : ℝ), Real.exp (-(r*s^beta)) ≤
      Real.exp (-r/2)*Real.exp (-((r/2)*s^beta)) := by
    intro s hs
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hp := Real.one_le_rpow hs.le hb.le
    nlinarith
  calc
    _ ≤ ∫ s in Ioi (1 : ℝ), Real.exp (-r/2)*Real.exp (-((r/2)*s^beta)) :=
      setIntegral_mono_on (hfull.mono_set hsub) ((hhalf.mono_set hsub).const_mul _)
        measurableSet_Ioi he
    _ = Real.exp (-r/2) * ∫ s in Ioi (1 : ℝ), Real.exp (-((r/2)*s^beta)) :=
      integral_const_mul _ _
    _ ≤ Real.exp (-r/2) * ∫ s in Ioi (0 : ℝ), Real.exp (-((r/2)*s^beta)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact setIntegral_mono_set hhalf (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
        (Filter.Eventually.of_forall fun _ hx => hsub hx)
    _ = _ := by rw [integral_slow_survival hb (half_pos hr)]

/-- A quantitative population formula for the exact power prototype, with
the original Gamma coefficient. Both grid errors are O(1/n); the omitted
half-line tail is exponentially small. This is an intermediate result,
not a substitute for the perturbed sampled-profile theorem. -/
theorem slow_prototype_population_error (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {beta r : ℝ} (hb : 0 < beta) (hr : 0 < r) :
    |(∑ i : Fin n, Real.exp (-(r*(samplePoint grid n i)^beta)))/(n : ℝ) -
      (1/r)^(1/beta)*Real.Gamma (1+1/beta)| ≤
      1/(n : ℝ) + Real.exp (-r/2)*((1/(r/2))^(1/beta)*Real.Gamma (1+1/beta)) := by
  have hi := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_slow_survival hb hr) zero_le_one
  have hnonneg : 0 ≤ ∫ s in Ioi (1 : ℝ), Real.exp (-(r*s^beta)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hdiff : |(∫ s in (0 : ℝ)..1, Real.exp (-(r*s^beta))) -
      (1/r)^(1/beta)*Real.Gamma (1+1/beta)| =
      ∫ s in Ioi (1 : ℝ), Real.exp (-(r*s^beta)) := by
    rw [integral_slow_survival hb hr] at hi
    rw [← hi]
    have heq : (1/r)^(1/beta)*Real.Gamma (1+1/beta) -
        (∫ s in Ioi (1 : ℝ), Real.exp (-(r*s^beta))) -
        (1/r)^(1/beta)*Real.Gamma (1+1/beta) =
        -(∫ s in Ioi (1 : ℝ), Real.exp (-(r*s^beta))) := by ring
    rw [heq, abs_neg, abs_of_nonneg hnonneg]
  calc
    _ ≤ |(∑ i : Fin n, Real.exp (-(r*(samplePoint grid n i)^beta)))/(n : ℝ) -
        ∫ s in (0 : ℝ)..1, Real.exp (-(r*s^beta))| +
        |(∫ s in (0 : ℝ)..1, Real.exp (-(r*s^beta))) -
          (1/r)^(1/beta)*Real.Gamma (1+1/beta)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (slow_survival_quadrature grid hn hb hr.le)
      (by rw [hdiff]; exact slow_survival_tail_bound hb hr)

end Luce.Section6
