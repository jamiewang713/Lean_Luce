import Luce.Section6DominationMatrixSmallRows

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- A finite matrix row with bounded weights, without a profile hypothesis. -/
theorem insertionDominationMatrix_weighted_row_le_size {n : ℕ} (w : Weights n)
    (r p : ℕ) (i : Fin n) (s : Finset (Fin n)) (v : Fin n → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hv : ∀ j ∈ s, v j ≤ B) :
    (∑ j ∈ s, v j*insertionDominationMatrix w r p i j) ≤ (n : ℝ)*B := by
  have hc : (s.card : ℝ) ≤ n := by
    have hcN : s.card ≤ n := by simpa using s.card_le_univ
    exact_mod_cast hcN
  calc
    _ ≤ ∑ _j ∈ s, B := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ B*insertionDominationMatrix w r p i j :=
          mul_le_mul_of_nonneg_right (hv j hj) (insertionDominationMatrix_nonneg w r p i j)
        _ ≤ B := by simpa using mul_le_mul_of_nonneg_left (insertionDominationMatrix_le_one w r p i j) hB
    _ = (s.card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hB

/-- The right weighted matrix row bound holds for all row sizes. -/
theorem PowerProfile.domination_matrix_right_weighted_row_all_n {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk0 : 0 ≤ kappa) (hk : kappa < beta) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n) (s : Finset (Fin n)),
      (∑ j ∈ s, ((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa*
        insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨C, N, hC, hN, hb⟩ := hp.domination_matrix_right_weighted_row hk0 hk r p hp1
  let T : ℝ := max N 1
  have hT : 0 < T := zero_lt_one.trans_le (le_max_right _ _)
  have hW : 0 < T^kappa := Real.rpow_pos_of_pos hT _
  refine ⟨C+T*T^kappa, add_pos hC (mul_pos hT hW), ?_⟩
  intro grid w hw n i s
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hlarge : N ≤ (n : ℝ)
  · exact (hb grid w hw n hn hlarge i s).trans (by have := mul_pos hT hW; linarith)
  · have hnT : (n : ℝ) ≤ T := (lt_of_not_ge hlarge).le.trans (le_max_left _ _)
    have ha : (1 : ℝ) ≤ terminalDepth i := by exact_mod_cast terminalDepth_pos i
    have hrow := insertionDominationMatrix_weighted_row_le_size (w n) r p i s
      (fun j => ((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa) hW.le (by
        intro j hj
        have hjn : (terminalDepth j : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n j.val)
        have hratio : (terminalDepth j : ℝ)/(terminalDepth i : ℝ) ≤ T := by
          apply (div_le_iff₀ (zero_lt_one.trans_le ha)).mpr
          nlinarith
        exact Real.rpow_le_rpow (by positivity) hratio hk0)
    exact hrow.trans ((mul_le_mul_of_nonneg_right hnT hW.le).trans (by linarith))

/-- The left weighted matrix row bound holds for all row sizes. -/
theorem PowerProfile.domination_matrix_left_weighted_row_all_n {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta kappa : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hk0 : 0 ≤ kappa) (hk : kappa < alpha) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n) (s : Finset (Fin n)),
      (∑ j ∈ s, (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa*
        insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨C, N, hC, hN, hb⟩ := hp.domination_matrix_left_weighted_row hk0 hk r p hp1
  let T : ℝ := max N 1
  have hT : 0 < T := zero_lt_one.trans_le (le_max_right _ _)
  have hW : 0 < T^kappa := Real.rpow_pos_of_pos hT _
  refine ⟨C+T*T^kappa, add_pos hC (mul_pos hT hW), ?_⟩
  intro grid w hw n i s
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  by_cases hlarge : N ≤ (n : ℝ)
  · exact (hb grid w hw n hn hlarge i s).trans (by have := mul_pos hT hW; linarith)
  · have hnT : (n : ℝ) ≤ T := (lt_of_not_ge hlarge).le.trans (le_max_left _ _)
    have hin : (i.val : ℝ)+1 ≤ n := by exact_mod_cast (show i.val+1 ≤ n by omega)
    have hrow := insertionDominationMatrix_weighted_row_le_size (w n) r p i s
      (fun j => (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa) hW.le (by
        intro j hj
        have hj1 : (1 : ℝ) ≤ (j.val : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) j.val; linarith
        have hratio : ((i.val : ℝ)+1)/((j.val : ℝ)+1) ≤ T := by
          apply (div_le_iff₀ (zero_lt_one.trans_le hj1)).mpr
          nlinarith
        exact Real.rpow_le_rpow (by positivity) hratio hk0)
    exact hrow.trans ((mul_le_mul_of_nonneg_right hnT hW.le).trans (by linarith))

end Luce.Section6
