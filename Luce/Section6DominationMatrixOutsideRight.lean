import Luce.Section6DominationMatrixSmallRows
import Luce.Section6RightOutsideInverseTarget
import Luce.Section6DominationMatrixCornerColumns

noncomputable section
open scoped ENNReal BigOperators
namespace Luce.Section6

theorem PowerProfile.domination_matrix_outside_right_target {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta sigma : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C H delta N : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, N ≤ (n : ℝ) → ∀ i j : Fin n, H ≤ (terminalDepth j : ℝ) →
      (terminalDepth j : ℝ)/(n : ℝ) ≤ delta → sigma ≤ (terminalDepth i : ℝ)/(n : ℝ) →
      insertionDominationMatrix (w n) r p i j ≤ C/(n : ℝ) := by
  obtain ⟨C, H, delta, N, hC, hH, hd, hd1, hN, hb⟩ := hp.right_outside_insertion_inverse_row hsigma hsigma1 r p hp1
  refine ⟨C, max H (8*(r : ℝ)+8), delta/2, N, hC, hH.trans_le (le_max_left _ _),
    half_pos hd, (half_lt_self hd).trans hd1, hN, ?_⟩
  intro grid w hw n hnN i j hjH hj hi
  have hn : 0 < n := by have := j.isLt; omega
  obtain ⟨removed, q, hremoved, hshift, hval⟩ := insertionDominationMatrix_attained (w n) r p i j
  have hgap : Nat.dist q (n-terminalDepth j) ≤ r+1 := by
    have hjrank : n-terminalDepth j = j.val := by unfold terminalDepth; omega
    rwa [hjrank]
  have hbuffer : 8*r+8 ≤ terminalDepth j := by
    exact_mod_cast (le_max_right H (8*(r : ℝ)+8)).trans hjH
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hq : q < (Finset.univ \ removed).card := by
    rw [hcard]
    exact (shifted_right_survivor_bounds hremoved (by unfold terminalDepth; omega) hbuffer hgap).1
  apply (ENNReal.ofReal_le_ofReal_iff (div_pos hC (Nat.cast_pos.mpr hn)).le).mp
  rw [hval]
  exact hb grid w hw n (terminalDepth j) hn hnN ((le_max_left _ _).trans hjH)
    hbuffer (hj.trans_lt (half_lt_self hd)) removed hremoved i hi ⟨q, hq⟩ p hp1 le_rfl hgap

theorem PowerProfile.domination_matrix_outside_right_column {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta sigma : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C H delta N : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, N ≤ (n : ℝ) → ∀ j : Fin n, H ≤ (terminalDepth j : ℝ) →
      (terminalDepth j : ℝ)/(n : ℝ) ≤ delta →
    ∀ s : Finset (Fin n), (∀ i ∈ s, sigma ≤ (terminalDepth i : ℝ)/(n : ℝ)) →
      (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨C, H, delta, N, hC, hH, hd, hd1, hN, hb⟩ := hp.domination_matrix_outside_right_target hsigma hsigma1 r p hp1
  refine ⟨C, H, delta, N, hC, hH, hd, hd1, hN, ?_⟩
  intro grid w hw n hnN j hjH hj s hs
  have hn : 0 < n := by have := j.isLt; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : (s.card : ℝ) ≤ n := by
    have hcN : s.card ≤ n := by simpa using s.card_le_univ
    exact_mod_cast hcN
  calc
    _ ≤ ∑ _i ∈ s, C/(n : ℝ) := Finset.sum_le_sum (fun i hi => hb grid w hw n hnN i j hjH hj (hs i hi))
    _ = (s.card : ℝ)*(C/(n : ℝ)) := by simp
    _ ≤ (n : ℝ)*(C/(n : ℝ)) := mul_le_mul_of_nonneg_right hc (div_pos hC hnR).le
    _ = C := by field_simp

/-- Right columns above a derived fixed depth, with every source and row
size included. Small rows use the proved matrix entry bound. -/
theorem PowerProfile.domination_matrix_right_column_above_cutoff {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C H delta : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ j : Fin n, H ≤ (terminalDepth j : ℝ) → (terminalDepth j : ℝ)/(n : ℝ) ≤ delta →
    ∀ s : Finset (Fin n), (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨B, H, sigma, hB, hH, hsigma, hsigma1, hb⟩ := hp.domination_matrix_right_corner_column r p hp1
  obtain ⟨D, K, delta, N, hD, hK, hd, hd1, hN, he⟩ := hp.domination_matrix_outside_right_column hsigma hsigma1 r p hp1
  refine ⟨B+D+N, max H K, min sigma delta, by positivity,
    hH.trans_le (le_max_left _ _), lt_min hsigma hd, (min_le_left _ _).trans_lt hsigma1, ?_⟩
  intro grid w hw n j hjH hj s
  classical
  by_cases hnN : N ≤ (n : ℝ)
  · let P : Fin n → Prop := fun i => (terminalDepth i : ℝ)/(n : ℝ) ≤ sigma
    let F : Fin n → ℝ := fun i => insertionDominationMatrix (w n) r p i j
    have hinside : (∑ i ∈ s.filter P, F i) ≤ B :=
      hb grid w hw n j ((le_max_left _ _).trans hjH) (hj.trans (min_le_left _ _))
        (s.filter P) (fun i hi => (Finset.mem_filter.mp hi).2)
    have houtside : (∑ i ∈ s.filter (fun i => ¬ P i), F i) ≤ D := by
      apply he grid w hw n hnN j ((le_max_right _ _).trans hjH) (hj.trans (min_le_right _ _))
      intro i hi
      exact (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
    change (∑ i ∈ s, F i) ≤ _
    rw [← Finset.sum_filter_add_sum_filter_not s P F]
    exact (add_le_add hinside houtside).trans (by linarith)
  · have hc : (s.card : ℝ) ≤ n := by
      have hcN : s.card ≤ n := by simpa using s.card_le_univ
      exact_mod_cast hcN
    calc
      _ ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum (fun i _ => insertionDominationMatrix_le_one (w n) r p i j)
      _ ≤ (n : ℝ) := by simpa using hc
      _ ≤ B+D+N := by linarith

end Luce.Section6
