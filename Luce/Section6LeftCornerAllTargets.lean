import Luce.Section6LeftCornerWeightedRow
import Luce.Section6EarlyLeftWeightedRow

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- The same-corner left weighted insertion row including every positive
source and target depth in the derived endpoint block. -/
theorem PowerProfile.left_corner_all_targets_weighted_row {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta kappa : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hk0 : 0 ≤ kappa) (hk : kappa < alpha) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C delta N : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1/2 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n), ((i.val : ℝ)+1)/(n : ℝ) ≤ delta →
    ∀ (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n)) (q : Fin n → ℕ)
      (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, ((j.val : ℝ)+1)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, H, delta, hB, hH, hd, hdh, hb⟩ :=
    hp.left_corner_weighted_insertion_row hk0 hk r p0 hp0
  obtain ⟨H0, hH0⟩ := exists_nat_gt H
  obtain ⟨D, N, hD, hN, he⟩ := hp.early_left_weighted_insertion_row hk0 hk.le r H0 p0
  refine ⟨D+B, delta, N, add_pos hD hB, hd, hdh, hN, ?_⟩
  intro grid w hw n hn hlarge i hismall s removed q p hpp hpp0 hs
  classical
  let P : Fin n → Prop := fun j => ((j.val : ℝ)+1) < H
  let g : Fin n → ℝ≥0∞ := fun j =>
    ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))
  have hearly : (∑ j ∈ s.filter P, g j) ≤ ENNReal.ofReal D := by
    apply he grid w hw n hn hlarge i (s.filter P) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    have hh : j.val+1 ≤ H0 := by
      have hhR : (j.val : ℝ)+1 ≤ H0 := (lt_trans hjP hH0).le
      exact_mod_cast hhR
    exact ⟨hh, (hs j hjs).2⟩
  have hmoderate : (∑ j ∈ s.filter (fun j => ¬ P j), g j) ≤ ENNReal.ofReal B := by
    apply hb grid w hw n hn i hismall (s.filter (fun j => ¬ P j)) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨le_of_not_gt hjP, hs j hjs⟩
  change (∑ j ∈ s, g j) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s P g]
  exact (add_le_add hearly hmoderate).trans_eq (ENNReal.ofReal_add hD.le hB.le).symm

end Luce.Section6
