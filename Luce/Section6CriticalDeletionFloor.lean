import Luce.Section6CriticalProfilePerturbation
import Luce.Section6LogExcursionAlgebra

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem critical_harmonic_tail_lower {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Real.log ((n : ℝ)/m) ≤ ∑ j ∈ Finset.Icc m n, 1/(j : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0 : ℝ) < n := hm0.trans_le (by exact_mod_cast hmn)
  have h := AntitoneOn.integral_le_sum_Ico hmn (f := fun x : ℝ => 1/x) (by
    intro x hx y hy hxy
    exact one_div_le_one_div_of_le (hm0.trans_le hx.1) hxy)
  rw [integral_one_div_of_pos hm0 hn0] at h
  exact h.trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
    (fun j _ _ => by positivity))

/-- Deleting at most m labels removes at most one unit from the
harmonic tail starting at m. This deliberately avoids rearrangement. -/
theorem critical_deleted_harmonic_lower {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (removed : Finset ℕ) (hcard : removed.card ≤ m) :
    Real.log ((n : ℝ)/m)-1 ≤ ∑ j ∈ Finset.Icc 1 n \ removed, 1/(j : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hbad : (∑ j ∈ Finset.Icc m n ∩ removed, 1/(j : ℝ)) ≤ 1 := by
    calc
      _ ≤ ∑ _j ∈ Finset.Icc m n ∩ removed, 1/(m : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact one_div_le_one_div_of_le hm0 (by exact_mod_cast
          (Finset.mem_Icc.mp (Finset.mem_inter.mp hj).1).1)
      _ = ((Finset.Icc m n ∩ removed).card : ℝ)/m := by simp; ring
      _ ≤ 1 := (div_le_one hm0).mpr (by exact_mod_cast
        (Finset.card_le_card Finset.inter_subset_right).trans hcard)
  have hsplit := Finset.sum_sdiff (Finset.inter_subset_left (s₁ := Finset.Icc m n) (s₂ := removed))
    (f := fun j : ℕ => 1/(j : ℝ))
  simp only [Finset.sdiff_inter_self_left] at hsplit
  have htail := critical_harmonic_tail_lower hm hmn
  have hsub : (∑ j ∈ Finset.Icc m n \ removed, 1/(j : ℝ)) ≤
      ∑ j ∈ Finset.Icc 1 n \ removed, 1/(j : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun j _ _ => by positivity)
    exact Finset.sdiff_subset_sdiff_left removed (Finset.Icc_subset_Icc hm le_rfl)
  linarith

theorem critical_label_image {n : ℕ} :
    Finset.univ.image (fun i : Fin n => i.val+1) = Finset.Icc 1 n := by
  ext j
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_Icc]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨by omega,i.isLt⟩
  · intro hj
    exact ⟨⟨j-1,by omega⟩,by dsimp; omega⟩

theorem critical_remaining_harmonic_lower {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (removed : Finset (Fin n)) (hcard : removed.card ≤ m) :
    Real.log ((n : ℝ)/m)-1 ≤
      ∑ i ∈ Finset.univ \ removed, 1/((i.val : ℝ)+1) := by
  have hinj : Function.Injective (fun i : Fin n => i.val+1) := fun i j h =>
    Fin.ext (Nat.add_right_cancel h)
  have h := critical_deleted_harmonic_lower hm hmn (removed.image (fun i => i.val+1))
    ((Finset.card_image_le).trans hcard)
  rw [← critical_label_image,← Finset.image_sdiff _ _ hinj,Finset.sum_image
    (fun i _ j _ hij => hinj hij)] at h
  simpa only [Nat.cast_add,Nat.cast_one] using h

/-- Sharp leading constant in the deterministic remaining-weight floor,
uniform over all sets of at most m deleted labels. -/
theorem CriticalProfile.remaining_weight_floor {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (grid : SamplingGrid) (w : WeightArray),
      SampledRates grid w f → ∀ (n m : ℕ), 1 ≤ m → m ≤ n →
      ∀ (removed : Finset (Fin n)), removed.card ≤ m →
        (n : ℝ)*(c*Real.log ((n : ℝ)/m)-C) ≤
          ∑ i ∈ Finset.univ \ removed, (w n).rate i := by
  obtain ⟨E,hE,herr⟩ := hp.sampled_error_average
  have hc : 0 < c := hp.2.2.1
  refine ⟨c+E,by positivity,?_⟩
  intro grid w hw n m hm hmn removed hcard
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < m) hmn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hEtotal : (∑ i : Fin n, |(w n).rate i-c/samplePoint grid n i|) ≤ E*n :=
    (div_le_iff₀ hn0).mp (herr grid w hw n hn)
  have hErem : (∑ i ∈ Finset.univ \ removed, |(w n).rate i-c/samplePoint grid n i|) ≤ E*n :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => abs_nonneg _)).trans hEtotal
  have hpoint (i : Fin n) : (c*n)*(1/((i.val : ℝ)+1)) ≤
      (w n).rate i+|(w n).rate i-c/samplePoint grid n i| := by
    have hs : (c*n)*(1/((i.val : ℝ)+1)) ≤ c/samplePoint grid n i := by
      calc
        _ = c/(((i.val : ℝ)+1)/n) := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_left hc.le (samplePoint_mem grid i).1
          (samplePoint_le_label grid i)
    have hab := le_abs_self (c/samplePoint grid n i-(w n).rate i)
    rw [abs_sub_comm] at hab
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ \ removed) (fun i _ => hpoint i)
  rw [← Finset.mul_sum,Finset.sum_add_distrib] at hsum
  have htail := mul_le_mul_of_nonneg_left (critical_remaining_harmonic_lower hm hmn removed hcard)
    (mul_pos hc hn0).le
  nlinarith

end Luce.Section6
