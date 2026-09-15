import Luce.Section6DominationMatrixFixedLeft
import Luce.Section6FiniteSampledRatios

noncomputable section
open scoped ENNReal
namespace Luce.Section6

/-- The exact manuscript rate-dependent bound for fixed earliest targets,
for every n. The finite-row absorption constant is proved from sampling. -/
theorem PowerProfile.domination_matrix_fixed_left_rate {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r H p : ℕ) (hp1 : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i j : Fin n), j.val+1 ≤ H →
      insertionDominationMatrix (w n) r p i j ≤ C*((w n).rate i/(n : ℝ)^alpha) := by
  obtain ⟨B, N, hB, hN, hb⟩ := hp.early_left_insertion_Lp r (H+r) p
  let T : ℝ := N+(r+(H+r)+1 : ℕ)
  obtain ⟨D, hD, hfinite⟩ := finite_sampled_rate_ratio_bound f alpha ⌈T⌉₊
  refine ⟨B+D, add_pos hB hD, ?_⟩
  intro grid w hw n i j hj
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hr : 0 ≤ (w n).rate i/(n : ℝ)^alpha :=
    div_nonneg ((w n).positive i).le (Real.rpow_nonneg hnR.le _)
  by_cases hlarge : T ≤ (n : ℝ)
  · have hlargeN : N ≤ (n : ℝ) := by
      dsimp [T] at hlarge
      have := Nat.cast_nonneg (α := ℝ) (r+(H+r)+1)
      linarith
    have hlargeNat : r+(H+r)+1 ≤ n := by
      have hh : ((r+(H+r)+1 : ℕ) : ℝ) ≤ n := by dsimp [T] at hlarge; linarith
      exact_mod_cast hh
    obtain ⟨removed, q, hremoved, hshift, hval⟩ := insertionDominationMatrix_attained (w n) r p i j
    have hqQ : q ≤ H+r := by unfold Nat.dist at hshift; omega
    have hcard : (Finset.univ \ removed).card = n-removed.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have hq : q < (Finset.univ \ removed).card := by rw [hcard]; omega
    have ht := hb grid w hw n hn hlargeN removed hremoved i ⟨q, hq⟩ p hqQ hp1 le_rfl
    have hM : insertionDominationMatrix (w n) r p i j ≤ B*((w n).rate i/(n : ℝ)^alpha) := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB.le hr)).mp
      rw [hval]
      exact ht
    exact hM.trans (mul_le_mul_of_nonneg_right (by linarith) hr)
  · have hnM : n ≤ ⌈T⌉₊ := by
      have hh : (n : ℝ) ≤ (⌈T⌉₊ : ℝ) := (lt_of_not_ge hlarge).le.trans (Nat.le_ceil T)
      exact_mod_cast hh
    exact (insertionDominationMatrix_le_one (w n) r p i j).trans
      ((hfinite grid w hw n hnM i).trans (mul_le_mul_of_nonneg_right (by linarith) hr))

end Luce.Section6
