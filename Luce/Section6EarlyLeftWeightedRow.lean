import Luce.Section6LeftWeightedRate
import Luce.Section6EarlyLeftLp

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- The fixed earliest-target contribution to the manuscript's left weighted
row, uniformly over all sources and target-dependent deletions and shifts.
The natural gap index may be zero; its finite membership is proved internally. -/
theorem PowerProfile.early_left_weighted_insertion_row {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta kappa : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hk0 : 0 ≤ kappa) (hk : kappa ≤ alpha) (r H p0 : ℕ) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, j.val+1 ≤ H ∧ (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, N, hB, hN, hb⟩ := hp.early_left_insertion_Lp r (H+r) p0
  obtain ⟨K, hK, hrate⟩ := hp.left_weighted_rate_bound
  refine ⟨((H : ℝ)+1)*(B*K), N+(r+(H+r)+1 : ℕ), by positivity, by positivity, ?_⟩
  intro grid w hw n hn hlarge i s removed q p hpp hpp0 hs
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlargeN : N ≤ (n : ℝ) := by
    have hh : (0 : ℝ) ≤ (r+(H+r)+1 : ℕ) := Nat.cast_nonneg _
    linarith
  have hlargeNat : r+(H+r)+1 ≤ n := by
    have hh : ((r+(H+r)+1 : ℕ) : ℝ) ≤ n := by linarith
    exact_mod_cast hh
  have hir := (w n).positive i
  have ha : 0 < (i.val : ℝ)+1 := by positivity
  have hterm : ∀ j ∈ s,
      ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
        eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
          (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (B*K) := by
    intro j hj
    obtain ⟨hjH, hremoved, hshift⟩ := hs j hj
    have hqQ : q j ≤ H+r := by unfold Nat.dist at hshift; omega
    have hcard : (Finset.univ \ removed j).card = n-(removed j).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have hq : q j < (Finset.univ \ removed j).card := by rw [hcard]; omega
    have he := hb grid w hw n hn hlargeN (removed j) hremoved i ⟨q j, hq⟩ p hqQ hpp hpp0
    have hh1 : (1 : ℝ) ≤ (j.val : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) j.val; linarith
    have hweight : (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa ≤ ((i.val : ℝ)+1)^kappa := by
      rw [Real.div_rpow ha.le (by positivity)]
      exact div_le_self (by positivity) (Real.one_le_rpow hh1 hk0)
    calc
      _ ≤ ENNReal.ofReal (((i.val : ℝ)+1)^kappa)*
          eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
            (p : ℝ≥0∞) (exponentialRace (w n)) :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hweight) zero_le
      _ ≤ ENNReal.ofReal (((i.val : ℝ)+1)^kappa)*
          ENNReal.ofReal (B*((w n).rate i/(n : ℝ)^alpha)) :=
        mul_le_mul_of_nonneg_left he zero_le
      _ = ENNReal.ofReal (B*(((i.val : ℝ)+1)^kappa*((w n).rate i/(n : ℝ)^alpha))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (hrate grid w hw n i kappa hk) hB.le)
  classical
  have hsub : s.image Fin.val ⊆ Finset.range H := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (by have hh := (hs j hj).1; omega)
  have hinj : Set.InjOn (Fin.val : Fin n → ℕ) s := by
    intro a ha b hb hab
    exact Fin.ext hab
  have hcard : s.card ≤ H := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hinj, Finset.card_range] at hh
    exact hh
  calc
    _ ≤ ∑ _j ∈ s, ENNReal.ofReal (B*K) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((s.card : ℝ)*(B*K)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => (mul_pos hB hK).le)]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh : (s.card : ℝ) ≤ H := by exact_mod_cast hcard
      exact mul_le_mul_of_nonneg_right (by linarith : (s.card : ℝ) ≤ (H : ℝ)+1) (mul_pos hB hK).le

end Luce.Section6
