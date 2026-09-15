import Luce.Section6WeightedPaths
import Luce.Section6DominationMatrixAllWeighted

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- All paths reaching left depth at most A have the manuscript's
weighted decay, from the original profile and sampling alone. -/
theorem PowerProfile.left_escaping_path_bound {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta kappa : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hk0 : 0 < kappa) (hk : kappa < alpha) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n k : ℕ) (v : Fin n) (A : ℝ), 0 < A →
      (∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        ∃ a, ((u a).val : ℝ)+1 ≤ A),
        forwardPathWeight (insertionDominationMatrix (w n) r p) v u) ≤
        (k : ℝ)*C^k*(1/((v.val : ℝ)+1)^kappa)/(1/A^kappa) := by
  classical
  obtain ⟨C, hC, hrow⟩ := hp.domination_matrix_row_bound_all_n r p hp1
  obtain ⟨D, hD, hweighted⟩ := hp.domination_matrix_left_weighted_row_all_n hk0.le hk r p hp1
  refine ⟨max C D, hC.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n k v A hA
  let M := insertionDominationMatrix (w n) r p
  let V : Fin n → ℝ := fun i => 1/((i.val : ℝ)+1)^kappa
  have hdepth (i : Fin n) : (0 : ℝ) < (i.val : ℝ)+1 := by positivity
  have hpow (i : Fin n) : 0 < ((i.val : ℝ)+1)^kappa := Real.rpow_pos_of_pos (hdepth i) _
  have hV (i : Fin n) : 0 < V i := one_div_pos.mpr (hpow i)
  have hwV (i : Fin n) : ∑ j, M i j * V j ≤ max C D * V i := by
    have he : (∑ j, M i j * V j) =
        (∑ j, (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa * M i j) * V i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [V]
      rw [Real.div_rpow (hdepth i).le (hdepth j).le]
      field_simp [ne_of_gt (hpow i), ne_of_gt (hpow j)]
    rw [he]
    exact mul_le_mul_of_nonneg_right
      ((hweighted grid w hw n i Finset.univ).trans (le_max_right _ _)) (hV i).le
  have hb := forward_path_escape_bound M
    (insertionDominationMatrix_nonneg (w n) r p) V (fun i => (hV i).le)
    (hC.le.trans (le_max_left _ _)) (one_div_pos.mpr (Real.rpow_pos_of_pos hA kappa))
    (fun i => (hrow grid w hw n i Finset.univ).trans (le_max_left _ _)) hwV k v
  apply le_trans _ hb
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    apply Finset.mem_filter.mpr
    obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hu).2
    exact ⟨Finset.mem_univ _, a, one_div_le_one_div_of_le (hpow (u a))
      (Real.rpow_le_rpow (hdepth (u a)).le ha hk0.le)⟩
  · intro u hu hnot
    exact Finset.prod_nonneg (fun a _ => insertionDominationMatrix_nonneg (w n) r p _ _)

end Luce.Section6
