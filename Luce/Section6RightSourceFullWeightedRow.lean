import Luce.Section6RightOutsideTargetsWeightedRow
import Luce.Section6RightEndpointWeightedRow

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Every target is covered for a source in the derived right block.
This includes paths crossing into the middle or the opposite endpoint. -/
theorem PowerProfile.right_source_full_weighted_insertion_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk0 : 0 ≤ kappa) (hk : kappa < beta) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C sigma N : ℝ, 0 < C ∧ 0 < sigma ∧ sigma < 1 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < sigma →
    ∀ (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, delta, N1, hB, hd, hdh, hN1, hb⟩ := hp.right_endpoint_weighted_insertion_row hk0 hk r p0 hp0
  obtain ⟨D, sigma, N2, hD, hsigma, hsigma1, hN2, he⟩ :=
    hp.right_outside_targets_weighted_row hk0 hk.le hd r p0 hp0
  refine ⟨B+D, sigma, max N1 N2, add_pos hB hD, hsigma, hsigma1,
    hN1.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge i hi s removed q p hpp hpp0 hs
  classical
  let P : Fin n → Prop := fun j => (terminalDepth j : ℝ)/(n : ℝ) ≤ delta
  let g : Fin n → ℝ≥0∞ := fun j =>
    ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))
  have hnear : (∑ j ∈ s.filter P, g j) ≤ ENNReal.ofReal B := by
    apply hb grid w hw n hn ((le_max_left _ _).trans hlarge) i (s.filter P) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨hjP, hs j hjs⟩
  have hfar : (∑ j ∈ s.filter (fun j => ¬ P j), g j) ≤ ENNReal.ofReal D := by
    apply he grid w hw n hn ((le_max_right _ _).trans hlarge) i hi
      (s.filter (fun j => ¬ P j)) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨(lt_of_not_ge hjP).le, hs j hjs⟩
  change (∑ j ∈ s, g j) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s P g]
  exact (add_le_add hnear hfar).trans_eq (ENNReal.ofReal_add hB.le hD.le).symm

end Luce.Section6
