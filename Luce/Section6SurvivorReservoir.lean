import Luce.Section6InteriorPopulationD

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- A positive fraction of interior labels survives at least as long as
an exponential clock of fixed rate M, even after bounded deletions. -/
theorem interior_deleted_survivor_reservoir {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 1)) (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x) :
    ∃ M : ℝ, 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 8 ≤ n → 16*r ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r → ∀ t : ℝ, 0 ≤ t →
      ((n : ℝ)/16)*Real.exp (-(M*t)) ≤ (n : ℝ)*deletedH (w n) removed t := by
  classical
  obtain ⟨d, M, hd, hM, hrate⟩ := interior_sampled_rate_bounds hf hpos
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) < 1)
  refine ⟨M, hM, ?_⟩
  intro grid w hw n r hn hr removed hremoved t ht
  obtain ⟨B, hcard, hlabels⟩ := exists_interior_label_block hn
  have hc : B.card ≤ (B \ removed).card+removed.card := by
    rw [Finset.card_sdiff]
    have h1 := Finset.card_le_card (Finset.inter_subset_left : removed ∩ B ⊆ removed)
    have h2 := Finset.card_le_card (Finset.inter_subset_right : removed ∩ B ⊆ B)
    omega
  have hcR : (B.card : ℝ) ≤ ((B \ removed).card : ℝ)+(removed.card : ℝ) := by exact_mod_cast hc
  have hrR : 16*(r : ℝ) ≤ n := by exact_mod_cast hr
  have hremR : (removed.card : ℝ) ≤ r := by exact_mod_cast hremoved
  have hcount : (n : ℝ)/16 ≤ ((B \ removed).card : ℝ) := by linarith
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have he : (n : ℝ)*deletedH (w n) removed t =
      ∑ i ∈ Finset.univ \ removed, survivalKernel t ((w n).rate i) := by
    unfold deletedH
    field_simp
  rw [he]
  calc
    _ ≤ ((B \ removed).card : ℝ)*Real.exp (-(M*t)) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = ∑ _i ∈ B \ removed, Real.exp (-(M*t)) := by simp
    _ ≤ ∑ i ∈ B \ removed, survivalKernel t ((w n).rate i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiB := (Finset.mem_sdiff.mp hi).1
      have hu := (hrate grid w hw n i (hlabels i hiB).1 (hlabels i hiB).2).2
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hu ht
      nlinarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.sdiff_subset_sdiff (Finset.subset_univ B) (Finset.Subset.refl removed))
      (fun i _ _ => (survivalKernel_pos _ _).le)

end Luce.Section6
