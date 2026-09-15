import Luce.Section6CriticalRootProbability
import Luce.Section6CriticalCyclePartition

noncomputable section
open MeasureTheory Function
open scoped BigOperators
namespace Luce.Section6

theorem critical_retained_probability_zero {n : ℕ} (w : Weights n) (k : ℕ)
    (S : Finset (Fin n)) {v : Fin n} (hv : v ∉ S) :
    (exponentialRace w).real (retainedMaximumCycleEvent k S v) = 0 := by
  have he : retainedMaximumCycleEvent k S v = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    apply hv
    apply he.2.2
    exact (Section5.mem_periodicOrbit_toFinset (raceRankPermutation e) v v).mpr
      (self_mem_periodicOrbit ((raceRankPermutation e).injective.mem_periodicPts v))
  rw [he]
  simp

theorem critical_retained_sum_bound {n M B : ℕ} (w : Weights n) (k : ℕ)
    (hM : 1 ≤ M) (hMB : M ≤ B) (hBn : B ≤ n)
    (hzB : (3/2 : ℝ) ≤ Real.log (n : ℝ)-Real.log (B : ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hprob : ∀ v ∈ criticalBlock n M B,
      (exponentialRace w).real (retainedMaximumCycleEvent k (criticalBlock n M B) v) ≤
        C*(Real.log ((n : ℝ)/((v.val : ℝ)+1)))^(-(3/2 : ℝ))/((v.val : ℝ)+1)) :
    (∫ e, (Section5.cycleCountWithin (raceRankPermutation e) (criticalBlock n M B) k : ℝ)
      ∂exponentialRace w) ≤ 3*C := by
  classical
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [critical_retained_expectation]
  have hs := critical_log_root_sum (n := (n : ℝ)) (p := (3/2 : ℝ)) (by norm_num) hM hMB hzB
  norm_num at hs
  calc
    _ = ∑ v ∈ criticalBlock n M B,
        (exponentialRace w).real (retainedMaximumCycleEvent k (criticalBlock n M B) v) := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _)
        (fun v _ hv => critical_retained_probability_zero w k _ hv)
    _ ≤ C*(∑ m ∈ Finset.Icc M B, (Real.log (n : ℝ)-Real.log (m : ℝ))^(-(3/2 : ℝ))/(m : ℝ)) := by
      rw [← critical_block_sum hM hBn,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v hv
      apply (hprob v hv).trans_eq
      push_cast
      rw [Real.log_div hn.ne' (by positivity)]
      ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hs hC]

end Luce.Section6
