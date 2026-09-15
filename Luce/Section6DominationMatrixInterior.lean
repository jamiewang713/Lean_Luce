import Luce.Section6DominationMatrix
import Luce.Section6InteriorTargetBound

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Every middle-target entry of the concrete matrix is O(1/n), uniformly
in its source. Maximization preserves the actual target bound. -/
theorem PowerProfile.domination_matrix_interior_target {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i j : Fin n), eps*(n : ℝ) ≤ (j.val : ℝ)+1 →
      (j.val : ℝ)+1 ≤ (1-eps)*(n : ℝ) →
      insertionDominationMatrix (w n) r p i j ≤ C/(n : ℝ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hp.interior_insertion_target_bound heps r p hp1
  refine ⟨C, max N ((8*(r : ℝ)+8)/eps), hC, hN.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge i j hl hu
  obtain ⟨removed, q, hremoved, hshift, he⟩ := insertionDominationMatrix_attained (w n) r p i j
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmargin : 8*(r : ℝ)+8 ≤ eps*(n : ℝ) := by
    have hh := (div_le_iff₀ heps).mp ((le_max_right _ _).trans hlarge)
    nlinarith
  have hbuffer : j.val+1+(2*r+2) ≤ n := by
    have hh : (j.val : ℝ)+1+(2*(r : ℝ)+2) ≤ n := by nlinarith
    exact_mod_cast hh
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hq : q < (Finset.univ \ removed).card := by unfold Nat.dist at hshift; omega
  apply (ENNReal.ofReal_le_ofReal_iff (div_pos hC hnR).le).mp
  rw [he]
  exact hb grid w hw n (j.val+1) hn ((le_max_left _ _).trans hlarge)
    (by simpa using hl) (by simpa using hu) removed hremoved i ⟨q, hq⟩ p
    (by simpa using hshift) hp1 le_rfl

/-- Middle columns of the same matrix are bounded, for arbitrary source subsets. -/
theorem PowerProfile.domination_matrix_interior_column {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (j : Fin n), eps*(n : ℝ) ≤ (j.val : ℝ)+1 →
      (j.val : ℝ)+1 ≤ (1-eps)*(n : ℝ) →
    ∀ s : Finset (Fin n), (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨C, N, hC, hN, hb⟩ := hp.domination_matrix_interior_target heps r p hp1
  refine ⟨C, N, hC, hN, ?_⟩
  intro grid w hw n hn hlarge j hl hu s
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : (s.card : ℝ) ≤ n := by
    have hcN : s.card ≤ n := by simpa using s.card_le_univ
    exact_mod_cast hcN
  calc
    _ ≤ ∑ _i ∈ s, C/(n : ℝ) := Finset.sum_le_sum (fun i _ => hb grid w hw n hn hlarge i j hl hu)
    _ = (s.card : ℝ)*(C/(n : ℝ)) := by simp
    _ ≤ (n : ℝ)*(C/(n : ℝ)) := mul_le_mul_of_nonneg_right hc (div_pos hC hnR).le
    _ = C := by field_simp

end Luce.Section6
