import Luce.Section6MonotoneQuadrature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

/-- Integral comparison with both endpoint terms, valid also for the
integrable negative-power singularity at zero. -/
theorem positive_power_sum_upper {z : ℝ} (hz : -1 < z) (M : ℕ) (hM : 0 < M) :
    (∑ k ∈ Finset.range M, ((k : ℝ)+1)^z) ≤
      (M : ℝ)^(z+1)/(z+1)+1+(M : ℝ)^z := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hM)
  have hz1 : 0 < z+1 := by linarith
  have hint : (∫ x in (1 : ℝ)..1+(N : ℝ), x^z) ≤
      ((N : ℝ)+1)^(z+1)/(z+1) := by
    rw [integral_rpow (Or.inl hz), Real.one_rpow, sub_div]
    have hnon : 0 ≤ 1/(z+1) := by positivity
    rw [add_comm (1 : ℝ) (N : ℝ)]
    linarith
  simp only [Nat.cast_succ]
  by_cases hz0 : 0 ≤ z
  · have hm : MonotoneOn (fun x : ℝ => x^z) (Icc 1 (1+(N : ℝ))) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow (by linarith [hx.1]) hxy hz0
    have hs := hm.sum_le_integral
    have hs' : (∑ k ∈ Finset.range N, ((k : ℝ)+1)^z) ≤
        ∫ x in (1 : ℝ)..1+(N : ℝ), x^z := by simpa only [add_comm] using hs
    rw [Finset.sum_range_succ]
    linarith
  · have hm : AntitoneOn (fun x : ℝ => x^z) (Icc 1 (1+(N : ℝ))) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (le_of_not_ge hz0)
    have hs := hm.sum_le_integral
    have hs' : (∑ k ∈ Finset.range N, (((k+1 : ℕ) : ℝ)+1)^z) ≤
        ∫ x in (1 : ℝ)..1+(N : ℝ), x^z := by
      simpa only [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hs
    rw [Finset.sum_range_succ']
    norm_num only [Nat.cast_zero, zero_add, Real.one_rpow]
    have hlast : 0 ≤ ((N : ℝ)+1)^z := Real.rpow_nonneg (by positivity) _
    linarith

end Luce.Section6
