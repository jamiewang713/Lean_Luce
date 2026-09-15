import Luce.Section65CenteredPoisson
import Luce.Section65GaussianMoments
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Luce.Section6

theorem gaussianMoment65_sum_rec (k : ℕ) :
    gaussianMoment65 1 (k+2) =
      ∑ j ∈ Finset.range (k+1), ((k+1).choose j : ℝ) *
        (0 : ℝ)^(k-j) * gaussianMoment65 1 j := by
  rw [Finset.sum_eq_single k]
  · simp [gaussianMoment65_rec, Nat.choose_succ_self_right]
  · intro j hj hne
    have hjk : j < k := lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hne
    simp [Nat.sub_ne_zero_of_lt hjk]
  · simp

/-- Fixed centered Poisson moments converge to the corresponding Gaussian
moments. The proof uses a finite recurrence at each order. -/
theorem scaledPoissonMoment65_tendsto (b : ℕ → ℝ)
    (hb : Tendsto b atTop atTop) (k : ℕ) :
    Tendsto (fun n => scaledPoissonMoment65 (b n) k) atTop
      (𝓝 (gaussianMoment65 1 k)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | k
    · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · rw [gaussianMoment65_sum_rec]
      have he : (fun n => scaledPoissonMoment65 (b n) (k+2)) =ᶠ[atTop]
          (fun n => ∑ j ∈ Finset.range (k+1), ((k+1).choose j : ℝ) *
            ((b n)⁻¹)^(k-j) * scaledPoissonMoment65 (b n) j) := by
        filter_upwards [hb.eventually_gt_atTop 0] with n hn
        exact scaledPoissonMoment65_rec (b n) (ne_of_gt hn) k
      apply Tendsto.congr' he.symm
      apply tendsto_finsetSum
      intro j hj
      exact (((tendsto_inv_atTop_zero.comp hb).pow (k-j)).const_mul _).mul
        (ih j (by have := Finset.mem_range.mp hj; omega))

end Luce.Section6
