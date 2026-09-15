import Luce.Section6DominationMatrix
import Luce.Section6GlobalWeightedRows

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Transfer an actual weighted row estimate to the finite maximum matrix.
The premise is discharged by the concrete profile theorems below. -/
theorem insertionDominationMatrix_weighted_row_transfer {n : ℕ} (w : Weights n)
    (r p : ℕ) (i : Fin n) (s : Finset (Fin n)) (v : Fin n → ℝ)
    (hv : ∀ j ∈ s, 0 ≤ v j) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ (removed : Fin n → Finset (Fin n)) (q : Fin n → ℕ),
      (∀ j ∈ s, (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
      (∑ j ∈ s, ENNReal.ofReal (v j)*
        eLpNorm (fun old => (deletedGapKernel w (removed j) old i (q j)).toReal)
          (p : ℝ≥0∞) (exponentialRace w)) ≤ ENNReal.ofReal C) :
    (∑ j ∈ s, v j*insertionDominationMatrix w r p i j) ≤ C := by
  obtain ⟨removed, q, hselect⟩ := insertionDominationMatrix_row_selection w r p i
  have he := hrow removed q (fun j _ => ⟨(hselect j).1, (hselect j).2.1⟩)
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  have hid : ENNReal.ofReal (∑ j ∈ s, v j*insertionDominationMatrix w r p i j) =
      ∑ j ∈ s, ENNReal.ofReal (v j)*
        eLpNorm (fun old => (deletedGapKernel w (removed j) old i (q j)).toReal)
          (p : ℝ≥0∞) (exponentialRace w) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg (hv j hj) (insertionDominationMatrix_nonneg w r p i j))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ENNReal.ofReal_mul (hv j hj), (hselect j).2.2]
  exact hid.trans_le he

/-- The concrete deterministic matrix has bounded unweighted rows. -/
theorem PowerProfile.domination_matrix_row_bound {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (r p : ℕ) (hp1 : 0 < p) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)),
      (∑ j ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨C, N, hC, hN, hb⟩ := hp.global_uniform_insertion_row r p hp1
  refine ⟨C, N, hC, hN, ?_⟩
  intro grid w hw n hn hlarge i s
  have he := insertionDominationMatrix_weighted_row_transfer (w n) r p i s (fun _ => 1)
    (fun _ _ => zero_le_one) hC.le (by
      intro removed q hs
      simpa only [ENNReal.ofReal_one, one_mul] using
        hb grid w hw n hn hlarge i s removed q p hp1 le_rfl hs)
  simpa only [one_mul] using he

/-- The same concrete matrix has the manuscript's right weighted rows. -/
theorem PowerProfile.domination_matrix_right_weighted_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk0 : 0 ≤ kappa) (hk : kappa < beta) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)),
      (∑ j ∈ s, ((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa*
        insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨C, N, hC, hN, hb⟩ := hp.global_right_weighted_insertion_row hk0 hk r p hp1
  refine ⟨C, N, hC, hN, ?_⟩
  intro grid w hw n hn hlarge i s
  apply insertionDominationMatrix_weighted_row_transfer (w n) r p i s
    (fun j => ((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa) (fun _ _ => by positivity) hC.le
  intro removed q hs
  exact hb grid w hw n hn hlarge i s removed q p hp1 le_rfl hs

/-- The same concrete matrix has the manuscript's left weighted rows. -/
theorem PowerProfile.domination_matrix_left_weighted_row {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta kappa : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hk0 : 0 ≤ kappa) (hk : kappa < alpha) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)),
      (∑ j ∈ s, (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa*
        insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨C, N, hC, hN, hb⟩ := hp.global_left_weighted_insertion_row hk0 hk r p hp1
  refine ⟨C, N, hC, hN, ?_⟩
  intro grid w hw n hn hlarge i s
  apply insertionDominationMatrix_weighted_row_transfer (w n) r p i s
    (fun j => (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa) (fun _ _ => by positivity) hC.le
  intro removed q hs
  exact hb grid w hw n hn hlarge i s removed q p hp1 le_rfl hs

end Luce.Section6
