import Luce.Section6DominationMatrix
import Luce.Section6LeftOutsideTarget
import Luce.Section6GapOffsets
import Luce.Section6DominationMatrixCornerColumns

noncomputable section
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Outside-left sources retain the sharper inverse-row target bound. -/
theorem PowerProfile.domination_matrix_outside_left_target {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta sigma : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1/2 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ i j : Fin n, 8*r+8 ≤ j.val+1 →
      ((j.val : ℝ)+1)/(n : ℝ) ≤ delta → sigma ≤ ((i.val : ℝ)+1)/(n : ℝ) →
      insertionDominationMatrix (w n) r p i j ≤ C/(n : ℝ) := by
  obtain ⟨C, delta, hC, hd, hds, hb⟩ := hp.left_outside_insertion_target_bound hsigma hsigma1 p
  refine ⟨C, min delta (1/2), hC, lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro grid w hw n i j hbuffer hj hi
  have hn : 0 < n := by have := j.isLt; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have htwice : 2*(j.val+1) ≤ n := by
    have ht := (div_le_iff₀ hnR).mp (hj.trans (min_le_right _ _))
    have ht' : 2*((j.val : ℝ)+1) ≤ n := by linarith
    exact_mod_cast ht'
  obtain ⟨removed, q, hremoved, hshift, hval⟩ := insertionDominationMatrix_attained (w n) r p i j
  have hgap : Nat.dist q (j.val+1-1) ≤ r+1 := by simpa using hshift
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hq : q < (Finset.univ \ removed).card := by
    rw [hcard]
    exact shifted_left_nonterminal hremoved hbuffer htwice hgap
  apply (ENNReal.ofReal_le_ofReal_iff (div_pos hC hnR).le).mp
  rw [hval]
  exact hb grid w hw n r (j.val+1) hn hbuffer
    (by simpa using hj.trans (min_le_left _ _)) removed hremoved i ⟨q, hq⟩ p hgap hi hp1 le_rfl

/-- Uniform column contribution from sources outside the fixed left block. -/
theorem PowerProfile.domination_matrix_outside_left_column {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta sigma : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1/2 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ j : Fin n, 8*r+8 ≤ j.val+1 → ((j.val : ℝ)+1)/(n : ℝ) ≤ delta →
    ∀ s : Finset (Fin n), (∀ i ∈ s, sigma ≤ ((i.val : ℝ)+1)/(n : ℝ)) →
      (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨C, delta, hC, hd, hdh, hb⟩ := hp.domination_matrix_outside_left_target hsigma hsigma1 r p hp1
  refine ⟨C, delta, hC, hd, hdh, ?_⟩
  intro grid w hw n j hbuffer hj s hs
  have hn : 0 < n := by have := j.isLt; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : (s.card : ℝ) ≤ n := by
    have hcN : s.card ≤ n := by simpa using s.card_le_univ
    exact_mod_cast hcN
  calc
    _ ≤ ∑ _i ∈ s, C/(n : ℝ) := Finset.sum_le_sum (fun i hi => hb grid w hw n i j hbuffer hj (hs i hi))
    _ = (s.card : ℝ)*(C/(n : ℝ)) := by simp
    _ ≤ (n : ℝ)*(C/(n : ℝ)) := mul_le_mul_of_nonneg_right hc (div_pos hC hnR).le
    _ = C := by field_simp

/-- Full left-endpoint columns above a derived fixed depth, now including
every source. Fixed initial target depths remain a separate obligation. -/
theorem PowerProfile.domination_matrix_left_column_above_cutoff {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C H delta : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ j : Fin n, H ≤ (j.val : ℝ)+1 → ((j.val : ℝ)+1)/(n : ℝ) ≤ delta →
    ∀ s : Finset (Fin n), (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨B, H, sigma, hB, hH, hsigma, hsigma1, hb⟩ := hp.domination_matrix_left_corner_column r p hp1
  obtain ⟨D, delta, hD, hd, hdh, he⟩ := hp.domination_matrix_outside_left_column hsigma hsigma1 r p hp1
  refine ⟨B+D, max H (8*(r : ℝ)+8), min sigma delta, add_pos hB hD,
    hH.trans_le (le_max_left _ _), lt_min hsigma hd, (min_le_left _ _).trans_lt hsigma1, ?_⟩
  intro grid w hw n j hjH hj s
  classical
  let P : Fin n → Prop := fun i => ((i.val : ℝ)+1)/(n : ℝ) ≤ sigma
  let F : Fin n → ℝ := fun i => insertionDominationMatrix (w n) r p i j
  have hinside : (∑ i ∈ s.filter P, F i) ≤ B :=
    hb grid w hw n j ((le_max_left _ _).trans hjH) (hj.trans (min_le_left _ _))
      (s.filter P) (fun i hi => (Finset.mem_filter.mp hi).2)
  have hbuffer : 8*r+8 ≤ j.val+1 := by
    exact_mod_cast (le_max_right H (8*(r : ℝ)+8)).trans hjH
  have houtside : (∑ i ∈ s.filter (fun i => ¬ P i), F i) ≤ D := by
    apply he grid w hw n j hbuffer (hj.trans (min_le_right _ _))
    intro i hi
    exact (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
  change (∑ i ∈ s, F i) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s P F]
  exact add_le_add hinside houtside

end Luce.Section6
