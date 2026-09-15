import Luce.Section4EndpointShellExpectationLimit
import Luce.Section4EndpointShellCover

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Luce

theorem sum_spatial_tail_le_shells {n J : ℕ} (hJ : 1 ≤ J)
    (hn : 2 ≤ (n : ℝ)*Real.exp (-(J : ℝ))) (p : Fin n → ℝ≥0∞) :
    (∑ i ∈ Finset.univ.filter (fun k : Fin n =>
      (1-Real.exp (-(J : ℝ))/2)*(n : ℝ) < (k.val : ℝ)+1), p i) ≤
      ∑ j ∈ Finset.range (n+1), if J ≤ j then ∑ i ∈ terminalShell n j, p i else 0 := by
  classical
  simp only [Finset.sum_filter]
  have hrewrite : (∑ j ∈ Finset.range (n+1), if J ≤ j then ∑ i ∈ terminalShell n j, p i else 0) =
      ∑ i : Fin n, ∑ j ∈ Finset.range (n+1),
        if J ≤ j then if i ∈ terminalShell n j then p i else 0 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : J ≤ j
    · simp only [if_pos hj, ← Finset.sum_filter]
      simp
    · simp only [if_neg hj, Finset.sum_const_zero]
  rw [hrewrite]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · obtain ⟨j, hj, hJj, hij⟩ := terminalShell_cover hJ i (spatial_tail_log_lower i hn hi)
    have h := Finset.single_le_sum (f := fun j =>
      if J ≤ j then if i ∈ terminalShell n j then p i else 0 else 0)
      (fun _ _ => bot_le) hj
    simpa only [if_pos hJj, if_pos hij] using h
  · exact bot_le

theorem spatial_tail_expectation_le_shells (w : WeightArray) (n J : ℕ) (hJ : 1 ≤ J)
    (hn : 2 ≤ (n : ℝ)*Real.exp (-(J : ℝ))) :
    ENNReal.ofReal (∫ e, (tailFixedPointCount e (1-Real.exp (-(J : ℝ))/2) : ℝ)
      ∂exponentialRace (w n)) ≤ nonnegativeTail (shellExpectationCost w) n J := by
  classical
  let block := Finset.univ.filter (fun k : Fin n =>
    (1-Real.exp (-(J : ℝ))/2)*(n : ℝ) < (k.val : ℝ)+1)
  have heq (e : Fin n → ℝ) : tailFixedPointCount e (1-Real.exp (-(J : ℝ))/2) =
      (block.filter fun i => raceRank e i = i.val+1).card := by
    simp only [tailFixedPointCount, block, Finset.filter_filter, rankOf_eq_raceRank_for_tail]
  simp_rw [heq]
  rw [block_fixedPoint_expectation_eq, ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
  apply le_trans (sum_spatial_tail_le_shells hJ hn
    (fun i => ENNReal.ofReal ((exponentialRace (w n)).real {e | raceRank e i = i.val+1})))
  have h := ENNReal.sum_le_tsum (Finset.range (n+1))
    (f := fun j => if J ≤ j then shellExpectationCost w n j else 0)
  apply le_trans _ h
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · rw [shellExpectationCost, ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
  · exact le_rfl

end Luce
