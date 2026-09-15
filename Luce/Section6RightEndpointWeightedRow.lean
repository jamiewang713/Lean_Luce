import Luce.Section6OutsideRightWeightedRow
import Luce.Section6RightCornerAllTargets

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Outside-right sources, with all terminal target depths included. -/
theorem PowerProfile.outside_right_all_weighted_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta sigma kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (hk : 0 ≤ kappa)
    (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C delta N : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1/2 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n), sigma ≤ (terminalDepth i : ℝ)/(n : ℝ) →
    ∀ (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n)) (q : Fin n → ℕ)
      (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, (terminalDepth j : ℝ)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, H, delta, N, hB, hH, hd, hdh, hN, hb⟩ :=
    hp.outside_right_weighted_insertion_row hsigma hsigma1 hk r p0 hp0
  obtain ⟨H0, hH0⟩ := exists_nat_gt H
  obtain ⟨D, hD, he⟩ := right_fixed_targets_weighted_row hk H0
  refine ⟨D+B, delta, N, add_pos hD hB, hd, hdh, hN, ?_⟩
  intro grid w hw n hn hlarge i hi s removed q p hpp hpp0 hs
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
    apply hb grid w hw n hn hlarge i hi (s.filter (fun j => ¬ P j)) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨le_of_not_gt hjP, hs j hjs⟩
  change (∑ j ∈ s, g j) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s P g]
  exact (add_le_add hterminal hmoderate).trans_eq (ENNReal.ofReal_add hD.le hB.le).symm

/-- Complete right-endpoint weighted insertion contribution for every source
label, including all fixed terminal targets and the infinite final gap. -/
theorem PowerProfile.right_endpoint_weighted_insertion_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk0 : 0 ≤ kappa) (hk : kappa < beta) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C delta N : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1/2 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, (terminalDepth j : ℝ)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, delta, hB, hd, hdh, hb⟩ := hp.right_corner_all_targets_weighted_row hk0 hk r p0 hp0
  have hd1 : delta < 1 := hdh.trans_lt (by norm_num)
  obtain ⟨D, eps, N, hD, heps, hepsh, hN, he⟩ := hp.outside_right_all_weighted_row hd hd1 hk0 r p0 hp0
  refine ⟨B+D, min delta eps, N, add_pos hB hD, lt_min hd heps, (min_le_left _ _).trans hdh, hN, ?_⟩
  intro grid w hw n hn hlarge i s removed q p hpp hpp0 hs
  by_cases hi : (terminalDepth i : ℝ)/(n : ℝ) ≤ delta
  · have hrow := hb grid w hw n hn i hi s removed q p hpp hpp0
      (fun j hj => ⟨((hs j hj).1).trans (min_le_left _ _), (hs j hj).2⟩)
    exact hrow.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · have hrow := he grid w hw n hn hlarge i (le_of_lt (lt_of_not_ge hi)) s removed q p hpp hpp0
      (fun j hj => ⟨((hs j hj).1).trans (min_le_right _ _), (hs j hj).2⟩)
    exact hrow.trans (ENNReal.ofReal_le_ofReal (by linarith))

end Luce.Section6
