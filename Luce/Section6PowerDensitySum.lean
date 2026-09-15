import Luce.Section6PowerDensityCell
import Luce.Section6PowerDensityIntegral
import Mathlib.Analysis.SumIntegralComparisons

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

/-- Uniform integer-depth sums for the ordinary active-endpoint kernels.
Both signs of p are covered, with no restriction on the positive scale A. -/
theorem power_density_positive_sum_bound {p d : ℝ} (hp : p ≠ 0) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), A*(h : ℝ)^(p-1)*Real.exp (-(d*A*(h : ℝ)^p))) ≤ C := by
  let F := (2 : ℝ)^|p-1|
  let rho := d/(2 : ℝ)^|p|
  have hF : 0 < F := by dsimp [F]; positivity
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have habs : 0 < |p| := abs_pos.mpr hp
  refine ⟨F*(1/(rho*|p|)), by positivity, ?_⟩
  intro A hA M
  let g : ℝ → ℝ := fun x => F*(A*x^(p-1)*Real.exp (-(rho*A*x^p)))
  have hg : IntegrableOn g (Ioi 0) := by
    exact (power_density_integrable hp hA hrho).const_mul F
  have hgi : IntegrableOn g (Ico (1 : ℝ) (M+1 : ℕ)) := hg.mono_set (by
    intro x hx
    exact lt_of_lt_of_le zero_lt_one hx.1)
  have hs := sum_Ico_le_integral_of_le (a := 1) (b := M+1) (by omega)
    (f := fun h : ℝ => A*h^(p-1)*Real.exp (-(d*A*h^p))) (g := g)
    (fun i hi x hx => by
      have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
      have hxR : x ≤ (i : ℝ)+1 := by simpa only [Nat.cast_add, Nat.cast_one] using hx.2.le
      exact power_density_cell_bound hiR hx.1 hxR hA hd p) (by simpa only [Nat.cast_one] using hgi)
  norm_num only [Nat.cast_one] at hs
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    dsimp [g]
    positivity
  have hbound : (∫ x in (1 : ℝ)..(M+1 : ℕ), g x) ≤ ∫ x in Ioi (0 : ℝ), g x := by
    rw [intervalIntegral.integral_of_le (by exact_mod_cast (show 1 ≤ M+1 by omega))]
    exact setIntegral_mono_set hg hnon (Filter.Eventually.of_forall (fun x hx =>
      zero_lt_one.trans hx.1))
  have he : (∫ x in Ioi (0 : ℝ), g x) = F*(1/(rho*|p|)) := by
    dsimp [g]
    rw [integral_const_mul, integral_power_density hp hA hrho]
  exact hs.trans (hbound.trans_eq he)

end Luce.Section6
