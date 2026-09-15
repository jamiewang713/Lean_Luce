import Luce.Section6MonotoneQuadrature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

/-- The first summand plus the integral bounds a decreasing depth sum. -/
theorem antitone_depth_sum_le {f : ℝ → ℝ} {A B : ℕ} (hAB : A ≤ B)
    (hf : AntitoneOn f (Set.Icc (A : ℝ) B)) :
    (∑ m ∈ Finset.Icc A B, f m) ≤ f A + ∫ x in (A : ℝ)..B, f x := by
  have hs := hf.sum_le_integral_Ico hAB
  have he : (∑ m ∈ Finset.Icc A B, f m) =
      f A + ∑ m ∈ Finset.Ico A B, f (m+1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : A < B+1)]
    congr 1
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Finset.sum_Ico_add' (fun m : ℕ => f m) A B 1).symm
  rw [he]
  exact add_le_add le_rfl (by simpa only [Nat.cast_add, Nat.cast_one] using hs)

/-- Uniform left excursion sum, in power form before the elementary
conversion to m^(-1)*(A/m)^kappa. -/
theorem left_excursion_depth_sum {kappa : ℝ} (hk : 0 < kappa)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (A : ℝ)^kappa * (∑ m ∈ Finset.Icc A B, (m : ℝ)^(-kappa-1)) ≤
      1 + 1/kappa := by
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hA0 : (0 : ℝ) < A := by linarith
  have hBr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hB0 : (0 : ℝ) < B := hA0.trans_le hBr
  have hf : AntitoneOn (fun x : ℝ => x^(-kappa-1)) (Set.Icc (A : ℝ) B) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hA0.trans_le hx.1) hxy (by linarith)
  have hs := antitone_depth_sum_le hAB hf
  have hz : (0 : ℝ) ∉ Set.uIcc (A : ℝ) B := by
    rw [Set.uIcc_of_le hBr]
    exact fun h => (not_le_of_gt hA0) h.1
  rw [integral_rpow (Or.inr ⟨by linarith, hz⟩)] at hs
  have hex : -kappa-1+1 = -kappa := by ring
  rw [hex] at hs
  have hpow : (A : ℝ)^kappa * (A : ℝ)^(-kappa) = 1 := by
    rw [← Real.rpow_add hA0, add_neg_cancel, Real.rpow_zero]
  have hfirst : (A : ℝ)^kappa * (A : ℝ)^(-kappa-1) = 1/(A : ℝ) := by
    rw [← Real.rpow_add hA0]
    convert Real.rpow_neg_one (A : ℝ) using 1 <;> ring
  have hpA : 0 ≤ (A : ℝ)^kappa := Real.rpow_nonneg hA0.le _
  have ht := mul_le_mul_of_nonneg_left hs hpA
  have hind : ((B : ℝ)^(-kappa)-(A : ℝ)^(-kappa))/(-kappa) ≤
      (A : ℝ)^(-kappa)/kappa := by
    have hb : 0 ≤ (B : ℝ)^(-kappa) := Real.rpow_nonneg hB0.le _
    rw [div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (by linarith) hk.le
  calc
    _ ≤ (A : ℝ)^kappa * ((A : ℝ)^(-kappa-1) + (A : ℝ)^(-kappa)/kappa) :=
      ht.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hind) hpA)
    _ = 1/(A : ℝ) + 1/kappa := by
      rw [mul_add, hfirst, ← mul_div_assoc, hpow]
    _ ≤ _ := add_le_add ((div_le_one hA0).mpr hAr) le_rfl

/-- Uniform right excursion sum for every positive exponent, including
both decreasing and increasing power summands. -/
theorem right_excursion_depth_sum {kappa : ℝ} (hk : 0 < kappa)
    {B : ℕ} (hB : 1 ≤ B) :
    (∑ m ∈ Finset.Icc 1 B, (m : ℝ)^(kappa-1))/(B : ℝ)^kappa ≤
      1 + 1/kappa := by
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hpB : 0 < (B : ℝ)^kappa := Real.rpow_pos_of_pos hB0 _
  apply (div_le_iff₀ hpB).mpr
  by_cases hk1 : kappa ≤ 1
  · have hf : AntitoneOn (fun x : ℝ => x^(kappa-1)) (Set.Icc (1 : ℝ) B) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    have hs := antitone_depth_sum_le hB (by simpa using hf)
    simp only [Nat.cast_one, Real.one_rpow] at hs
    rw [integral_rpow (Or.inl (by linarith : -1 < kappa-1))] at hs
    have he : kappa-1+1 = kappa := by ring
    rw [he, Real.one_rpow] at hs
    have hpow : (1 : ℝ) ≤ (B : ℝ)^kappa := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hBr hk.le
    have hinv : 0 < 1/kappa := one_div_pos.mpr hk
    have hbound : 1 + ((B : ℝ)^kappa-1)/kappa ≤ (1+1/kappa)*(B : ℝ)^kappa := by
      field_simp
      nlinarith
    exact hs.trans hbound
  · have hsum : (∑ m ∈ Finset.Icc 1 B, (m : ℝ)^(kappa-1)) ≤
        (B : ℝ)*(B : ℝ)^(kappa-1) := by
      calc
        _ ≤ ∑ _m ∈ Finset.Icc 1 B, (B : ℝ)^(kappa-1) := by
          apply Finset.sum_le_sum
          intro m hm
          have hmB : (m : ℝ) ≤ B := by exact_mod_cast (Finset.mem_Icc.mp hm).2
          exact Real.rpow_le_rpow (Nat.cast_nonneg _) hmB (by linarith)
        _ = _ := by simp
    have he : (B : ℝ)*(B : ℝ)^(kappa-1) = (B : ℝ)^kappa := by
      nth_rw 1 [← Real.rpow_one (B : ℝ)]
      rw [← Real.rpow_add hB0]
      congr 1
      ring
    rw [he] at hsum
    exact hsum.trans (by have := mul_nonneg (show 0 ≤ 1/kappa by positivity) hpB.le; nlinarith)

/-- Literal manuscript left excursion sum, uniformly in both integer
depth cutoffs. -/
theorem left_excursion_kernel_sum {kappa : ℝ} (hk : 0 < kappa)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ m ∈ Finset.Icc A B, (1/(m : ℝ))*((A : ℝ)/(m : ℝ))^kappa) ≤
      1 + 1/kappa := by
  have he : (∑ m ∈ Finset.Icc A B, (1/(m : ℝ))*((A : ℝ)/(m : ℝ))^kappa) =
      (A : ℝ)^kappa * ∑ m ∈ Finset.Icc A B, (m : ℝ)^(-kappa-1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 : (0 : ℝ) < m := by
      exact_mod_cast (show 0 < m by have := (Finset.mem_Icc.mp hm).1; omega)
    rw [Real.div_rpow (Nat.cast_nonneg _) hm0.le,
      Real.rpow_sub hm0, Real.rpow_one, Real.rpow_neg hm0.le]
    ring
  rw [he]
  exact left_excursion_depth_sum hk hA hAB

/-- Literal manuscript right excursion sum. Dropping the lower cutoff
uses nonnegativity; the constant remains independent of A and B. -/
theorem right_excursion_kernel_sum {kappa : ℝ} (hk : 0 < kappa)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ m ∈ Finset.Icc A B, (1/(m : ℝ))*((m : ℝ)/(B : ℝ))^kappa) ≤
      1 + 1/kappa := by
  have he : (∑ m ∈ Finset.Icc 1 B, (1/(m : ℝ))*((m : ℝ)/(B : ℝ))^kappa) =
      (∑ m ∈ Finset.Icc 1 B, (m : ℝ)^(kappa-1))/(B : ℝ)^kappa := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 : (0 : ℝ) < m := by
      exact_mod_cast (show 0 < m by have := (Finset.mem_Icc.mp hm).1; omega)
    rw [Real.div_rpow hm0.le (Nat.cast_nonneg _), Real.rpow_sub hm0, Real.rpow_one]
    ring
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 B, (1/(m : ℝ))*((m : ℝ)/(B : ℝ))^kappa := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_Icc.mpr ⟨hA.trans (Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2⟩
      · intro m hm hnot
        positivity
    _ = _ := he
    _ ≤ _ := right_excursion_depth_sum hk (hA.trans hAB)

end Luce.Section6
