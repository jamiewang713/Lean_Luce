import Luce.Section6InactiveKernelSubset
import Luce.Section6LogarithmicKernelIdentity

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Actual insertion norms summed over arbitrary inactive-right targets,
including final gaps and target-dependent bounded deletions and shifts. -/
theorem PowerProfile.inactive_right_insertion_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c : ℝ} (hp : PowerProfile f left (.finite c))
    (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, N ≤ n →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, 16384*terminalDepth j ≤ n ∧ (removed j).card ≤ r ∧
      Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, d, N, hB, hd, hN, hb⟩ := hp.inactive_right_all_gaps_power_kernel r p0 hp0
  obtain ⟨A, hA, ha⟩ := inactive_terminal_kernel_subset_bound hd
  refine ⟨B*A, N, mul_pos hB hA, hN, ?_⟩
  intro grid w hw n hn i s removed q p hpp hpp0 hs
  let g : Fin n → ℝ := fun j => ((w n).rate i/(terminalDepth j : ℝ))*
    ((terminalDepth j : ℝ)/(n : ℝ))^(d*(w n).rate i)+
      Real.exp (-d*Real.sqrt ((n : ℝ)*(terminalDepth j : ℝ)))
  have hi := (w n).positive i
  have hg (j : Fin n) : 0 ≤ B*g j := by dsimp [g]; positivity
  calc
    _ ≤ ∑ j ∈ s, ENNReal.ofReal (B*g j) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hrange, hremoved, hshift⟩ := hs j hj
      have he : n-terminalDepth j = j.val := by unfold terminalDepth; omega
      have hdepth : 1 ≤ terminalDepth j := terminalDepth_pos j
      exact hb grid w hw n (terminalDepth j) hn hdepth hrange (removed j) hremoved
        i (q j) p (by simpa only [he] using hshift) hpp hpp0
    _ = ENNReal.ofReal (∑ j ∈ s, B*g j) :=
      (ENNReal.ofReal_sum_of_nonneg (fun j _ => hg j)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (ha n ((w n).rate i) (by omega) hi s (fun j hj => (hs j hj).1)) hB.le

end Luce.Section6
