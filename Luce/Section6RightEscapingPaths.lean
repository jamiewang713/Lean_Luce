import Luce.Section6WeightedPaths
import Luce.Section6DominationMatrixAllWeighted

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The global right weighted row controls all paths which reach beyond B,
including paths through the middle or the other endpoint. -/
theorem PowerProfile.right_escaping_path_bound {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk0 : 0 < kappa) (hk : kappa < beta) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n k : ℕ) (v : Fin n) (B : ℝ), 0 < B →
      (∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        ∃ a, B ≤ (terminalDepth (u a) : ℝ)),
        forwardPathWeight (insertionDominationMatrix (w n) r p) v u) ≤
        (k : ℝ)*C^k*(terminalDepth v : ℝ)^kappa/B^kappa := by
  classical
  obtain ⟨C, hC, hrow⟩ := hp.domination_matrix_row_bound_all_n r p hp1
  obtain ⟨D, hD, hweighted⟩ := hp.domination_matrix_right_weighted_row_all_n hk0.le hk r p hp1
  refine ⟨max C D, hC.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n k v B hB
  let M := insertionDominationMatrix (w n) r p
  let V : Fin n → ℝ := fun i => (terminalDepth i : ℝ)^kappa
  have hdepth (i : Fin n) : (0 : ℝ) < terminalDepth i := by
    exact_mod_cast terminalDepth_pos i
  have hV (i : Fin n) : 0 < V i := Real.rpow_pos_of_pos (hdepth i) _
  have hwV (i : Fin n) : ∑ j, M i j * V j ≤ max C D * V i := by
    have he : (∑ j, M i j * V j) =
        (∑ j, ((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa * M i j) * V i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [V]
      rw [Real.div_rpow (hdepth j).le (hdepth i).le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos (hdepth i) kappa)]
    rw [he]
    exact mul_le_mul_of_nonneg_right
      ((hweighted grid w hw n i Finset.univ).trans (le_max_right _ _)) (hV i).le
  have hb := forward_path_escape_bound M
    (insertionDominationMatrix_nonneg (w n) r p) V (fun i => (hV i).le)
    (hC.le.trans (le_max_left _ _)) (Real.rpow_pos_of_pos hB kappa)
    (fun i => (hrow grid w hw n i Finset.univ).trans (le_max_left _ _)) hwV k v
  apply le_trans _ hb
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    apply Finset.mem_filter.mpr
    obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hu).2
    exact ⟨Finset.mem_univ _, a, Real.rpow_le_rpow hB.le ha hk0.le⟩
  · intro u hu hnot
    exact Finset.prod_nonneg (fun a _ => insertionDominationMatrix_nonneg (w n) r p _ _)

end Luce.Section6
