import Luce.Section6RightCornerWeightedRow
import Luce.Section6RightFixedWeightedRow

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- The right-corner weighted insertion row at every positive target depth,
including fixed terminal targets and the infinite final gap. -/
theorem PowerProfile.right_corner_all_targets_weighted_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk0 : 0 ≤ kappa) (hk : kappa < beta) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1/2 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n →
    ∀ (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) ≤ delta →
    ∀ (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n)) (q : Fin n → ℕ)
      (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, (terminalDepth j : ℝ)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, H, delta, hB, hH, hd, hdh, hb⟩ :=
    hp.right_corner_weighted_insertion_row hk0 hk r p0 hp0
  obtain ⟨H0, hH0⟩ := exists_nat_gt H
  obtain ⟨D, hD, he⟩ := right_fixed_targets_weighted_row hk0 H0
  refine ⟨D+B, delta, add_pos hD hB, hd, hdh, ?_⟩
  intro grid w hw n hn i hismall s removed q p hpp hpp0 hs
  classical
  let P : Fin n → Prop := fun j => (terminalDepth j : ℝ) < H
  let g : Fin n → ℝ≥0∞ := fun j =>
    ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))
  have hterminal : (∑ j ∈ s.filter P, g j) ≤ ENNReal.ofReal D := by
    apply he n (w n) i (s.filter P) removed q (p : ℝ≥0∞)
    intro j hj
    have hhR : (terminalDepth j : ℝ) ≤ H0 := (lt_trans (Finset.mem_filter.mp hj).2 hH0).le
    exact_mod_cast hhR
  have hmoderate : (∑ j ∈ s.filter (fun j => ¬ P j), g j) ≤ ENNReal.ofReal B := by
    apply hb grid w hw n hn i hismall (s.filter (fun j => ¬ P j)) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨le_of_not_gt hjP, hs j hjs⟩
  change (∑ j ∈ s, g j) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s P g]
  exact (add_le_add hterminal hmoderate).trans_eq (ENNReal.ofReal_add hD.le hB.le).symm

end Luce.Section6
