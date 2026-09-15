import Luce.Section6CriticalDeletionFloor

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem critical_drawn_labels {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    Finset.univ \ remaining π k = (Finset.Iio k).image π := by
  classical
  ext i
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,remaining,Finset.mem_filter,
    not_le,Finset.mem_image,Finset.mem_Iio]
  constructor
  · intro hi
    exact ⟨π.symm i,hi,π.apply_symm_apply i⟩
  · rintro ⟨j,hj,rfl⟩
    simpa using hj

theorem critical_drawn_card {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (Finset.univ \ remaining π k).card = k.val := by
  rw [critical_drawn_labels,Finset.card_image_of_injective _ π.injective]
  simp

/-- A uniform deterministic envelope for every early predictable fixed
point probability, including the first positions. -/
theorem CriticalProfile.predictable_envelope {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ A Z : ℝ, 0 < A ∧ 1 ≤ Z ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (π : Equiv.Perm (Fin n)) (k : Fin n),
        Z ≤ Real.log ((n : ℝ)/((k.val : ℝ)+1)) →
        (c/2)*(n : ℝ)*Real.log ((n : ℝ)/((k.val : ℝ)+1)) ≤ (w n).total (remaining π k) ∧
        predictableChance (w n) π k ≤
          A/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1))) := by
  obtain ⟨C,hC,hfloor⟩ := hp.remaining_weight_floor
  obtain ⟨a,b,ha,hb,hrate⟩ := hp.sampled_global_comparison
  have hc : 0 < c := hp.2.2.1
  refine ⟨2*b/c,max 1 (2*C/c),by positivity,le_max_left _ _,?_⟩
  intro grid w hw n π k hz
  have hn : 0 < n := Nat.zero_lt_of_lt k.isLt
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hk0 : (0 : ℝ) < (k.val : ℝ)+1 := by positivity
  have hz1 : 1 ≤ Real.log ((n : ℝ)/((k.val : ℝ)+1)) := (le_max_left _ _).trans hz
  have hz0 : 0 < Real.log ((n : ℝ)/((k.val : ℝ)+1)) := lt_of_lt_of_le zero_lt_one hz1
  have hzC : 2*C ≤ c*Real.log ((n : ℝ)/((k.val : ℝ)+1)) :=
    by simpa only [mul_comm] using (div_le_iff₀ hc).mp ((le_max_right _ _).trans hz)
  have hrem := hfloor grid w hw n (k.val+1) (by omega) k.isLt
    (Finset.univ \ remaining π k) (by rw [critical_drawn_card]; omega)
  have hdub : Finset.univ \ (Finset.univ \ remaining π k) = remaining π k :=
    Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
  rw [hdub] at hrem
  simp only [Nat.cast_add,Nat.cast_one] at hrem
  have hlow : (c/2)*(n : ℝ)*Real.log ((n : ℝ)/((k.val : ℝ)+1)) ≤
      (w n).total (remaining π k) := by
    change _ ≤ ∑ i ∈ remaining π k, (w n).rate i
    nlinarith [mul_le_mul_of_nonneg_left hzC hn0.le]
  refine ⟨hlow,?_⟩
  have hden : 0 < (c/2)*(n : ℝ)*Real.log ((n : ℝ)/((k.val : ℝ)+1)) := by positivity
  calc
    _ ≤ (w n).rate k/(w n).total (remaining π k) := predictableChance_le_rate_div _ _ _
    _ ≤ (b*n/((k.val : ℝ)+1))/((c/2)*n*Real.log ((n : ℝ)/((k.val : ℝ)+1))) :=
      (div_le_div_of_nonneg_left ((w n).positive k).le hden hlow).trans
        (div_le_div_of_nonneg_right (hrate grid w hw n k).2 hden.le)
    _ = _ := by field_simp

end Luce.Section6
