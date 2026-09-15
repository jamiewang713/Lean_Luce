import Luce.Section6EarlyLeftWeightedRow
import Luce.Section6OutsideLeftWeightedRow

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Complete outside-source contribution to the left weighted row in a
derived endpoint block, including every fixed earliest target. -/
theorem PowerProfile.outside_left_all_weighted_row {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta sigma kappa : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hk0 : 0 ≤ kappa) (hk : kappa < alpha) (r p0 : ℕ) :
    ∃ C delta N : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ sigma ∧ delta ≤ 1/2 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ),
    sigma ≤ ((i.val : ℝ)+1)/(n : ℝ) → 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, ((j.val : ℝ)+1)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, N, hB, hN, hb⟩ := hp.early_left_weighted_insertion_row hk0 hk.le r (8*r+8) p0
  obtain ⟨D, delta, hD, hd, hds, hdh, hdrow⟩ :=
    hp.outside_left_manuscript_weighted_row hsigma hsigma1 hk0 hk p0
  refine ⟨B+D, delta, N, add_pos hB hD, hd, hds, hdh, hN, ?_⟩
  intro grid w hw n hn hlarge i s removed q p hi hpp hpp0 hs
  classical
  let P : Fin n → Prop := fun j => j.val+1 < 8*r+8
  let g : Fin n → ℝ≥0∞ := fun j =>
    ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))
  have hearly : (∑ j ∈ s.filter P, g j) ≤ ENNReal.ofReal B := by
    apply hb grid w hw n hn hlarge i (s.filter P) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨le_of_lt hjP, (hs j hjs).2⟩
  have hmoderate : (∑ j ∈ s.filter (fun j => ¬ P j), g j) ≤ ENNReal.ofReal D := by
    apply hdrow grid w hw n r hn i (s.filter (fun j => ¬ P j)) removed q p hi hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨le_of_not_gt hjP, hs j hjs⟩
  change (∑ j ∈ s, g j) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s P g]
  exact (add_le_add hearly hmoderate).trans_eq (ENNReal.ofReal_add hB.le hD.le).symm

end Luce.Section6
