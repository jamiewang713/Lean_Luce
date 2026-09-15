import Luce.Section6DominationMatrixSmallRows
import Luce.Section6EarlyLeftLp
import Luce.Section6LeftWeightedRate
import Luce.Section6SampledWeightedSubsets
import Luce.Section6DominationMatrixOutsideLeft

noncomputable section
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Fixed earliest targets retain summable inverse-power decay in the
source depth. All constants come from the original sampled profile. -/
theorem PowerProfile.domination_matrix_fixed_left_power {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r H p : ℕ) (hp1 : 0 < p) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, N ≤ (n : ℝ) → ∀ i j : Fin n, j.val+1 ≤ H →
      insertionDominationMatrix (w n) r p i j ≤ C*((i.val : ℝ)+1)^(-alpha) := by
  obtain ⟨B, N, hB, hN, hb⟩ := hp.early_left_insertion_Lp r (H+r) p
  obtain ⟨K, hK, hrate⟩ := hp.left_weighted_rate_bound
  refine ⟨B*K, N+(r+(H+r)+1 : ℕ), mul_pos hB hK, by positivity, ?_⟩
  intro grid w hw n hlarge i j hj
  have hn : 0 < n := by have := j.isLt; omega
  have hlargeN : N ≤ (n : ℝ) := by have := Nat.cast_nonneg (α := ℝ) (r+(H+r)+1); linarith
  have hlargeNat : r+(H+r)+1 ≤ n := by
    have ht : ((r+(H+r)+1 : ℕ) : ℝ) ≤ n := by linarith
    exact_mod_cast ht
  obtain ⟨removed, q, hremoved, hshift, hval⟩ := insertionDominationMatrix_attained (w n) r p i j
  have hqQ : q ≤ H+r := by unfold Nat.dist at hshift; omega
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hq : q < (Finset.univ \ removed).card := by rw [hcard]; omega
  have ht := hb grid w hw n hn hlargeN removed hremoved i ⟨q, hq⟩ p hqQ hp1 le_rfl
  have ha : 0 < (i.val : ℝ)+1 := by positivity
  have hrate' : (w n).rate i/(n : ℝ)^alpha ≤ K*((i.val : ℝ)+1)^(-alpha) := by
    have hs := hrate grid w hw n i alpha le_rfl
    rw [Real.rpow_neg ha.le, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos ha alpha)).mpr (by simpa only [mul_comm] using hs)
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  rw [hval]
  exact ht.trans (ENNReal.ofReal_le_ofReal (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrate' hB.le))

/-- Every fixed initial target column is uniformly bounded, including
small rows. Summability follows from the manuscript's alpha>1. -/
theorem PowerProfile.domination_matrix_fixed_left_column {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r H p : ℕ) (hp1 : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ j : Fin n, j.val+1 ≤ H →
    ∀ s : Finset (Fin n), (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨B, N, hB, hN, hb⟩ := hp.domination_matrix_fixed_left_power r H p hp1
  have ha : 1 < alpha := hp.2.2.1.2.1
  have hs : Summable (fun a : ℕ => (a : ℝ)^(-alpha)) := Real.summable_nat_rpow.mpr (by linarith)
  let D : ℝ := max 1 (∑' a : ℕ, (a : ℝ)^(-alpha))
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨B*D+N, by positivity, ?_⟩
  intro grid w hw n j hj s
  by_cases hnN : N ≤ (n : ℝ)
  · have hinj : Function.Injective (fun i : Fin n => i.val+1) := by
      intro a b hab
      apply Fin.ext
      change a.val+1 = b.val+1 at hab
      omega
    have hf := positive_depth_subset_sum_le s (fun i => i.val+1) hinj
      (fun i => ⟨by omega, Nat.succ_le_of_lt i.isLt⟩)
      (fun a => (a : ℝ)^(-alpha)) (fun a _ => by positivity)
    have hsum : (∑ i ∈ s, ((i.val : ℝ)+1)^(-alpha)) ≤ D := by
      have ht := hs.sum_le_tsum (Finset.Ico 1 (n+1)) (fun a _ => by positivity)
      simpa only [Nat.cast_add, Nat.cast_one] using hf.trans (ht.trans (le_max_right 1 _))
    calc
      _ ≤ ∑ i ∈ s, B*((i.val : ℝ)+1)^(-alpha) :=
        Finset.sum_le_sum (fun i _ => hb grid w hw n hnN i j hj)
      _ = B*(∑ i ∈ s, ((i.val : ℝ)+1)^(-alpha)) := (Finset.mul_sum _ _ _).symm
      _ ≤ B*D := mul_le_mul_of_nonneg_left hsum hB.le
      _ ≤ B*D+N := by linarith
  · have hc : (s.card : ℝ) ≤ n := by
      have hcN : s.card ≤ n := by simpa using s.card_le_univ
      exact_mod_cast hcN
    calc
      _ ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum (fun i _ => insertionDominationMatrix_le_one (w n) r p i j)
      _ ≤ (n : ℝ) := by simpa using hc
      _ ≤ B*D+N := by nlinarith

/-- Complete active-left column bound: every positive target depth in the
derived endpoint block, every source subset and every row size. -/
theorem PowerProfile.domination_matrix_left_column {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ j : Fin n, ((j.val : ℝ)+1)/(n : ℝ) ≤ delta →
    ∀ s : Finset (Fin n), (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨B, H, delta, hB, hH, hd, hd1, hb⟩ := hp.domination_matrix_left_column_above_cutoff r p hp1
  obtain ⟨H0, hH0⟩ := exists_nat_gt H
  obtain ⟨D, hD, he⟩ := hp.domination_matrix_fixed_left_column r H0 p hp1
  refine ⟨B+D, delta, add_pos hB hD, hd, hd1, ?_⟩
  intro grid w hw n j hj s
  by_cases hdepth : H ≤ (j.val : ℝ)+1
  · exact (hb grid w hw n j hdepth hj s).trans (by linarith)
  · have hjH : j.val+1 ≤ H0 := by
      have ht : (j.val : ℝ)+1 ≤ H0 := (lt_of_not_ge hdepth).le.trans hH0.le
      exact_mod_cast ht
    exact (he grid w hw n j hjH s).trans (by linarith)

end Luce.Section6
