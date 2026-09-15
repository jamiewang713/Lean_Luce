import Luce.Section6ExcursionDepthSums
import Luce.Section6Lemma67Definitions

noncomputable section
open MeasureTheory Function
open scoped BigOperators
namespace Luce.Section6

theorem cornerDistance_pos67 {n : ℕ} (side : Corner) (v : Fin n) :
    0 < cornerDistance side v := by
  cases side <;> simp only [cornerDistance] <;> omega

theorem cornerDistance_injective67 {n : ℕ} (side : Corner) :
    Injective (cornerDistance side : Fin n → ℕ) := by
  intro i j hij
  apply Fin.ext
  cases side <;> simp only [cornerDistance] at hij <;> omega

theorem log_distance_right_ratio {m z R : ℝ} (hm : 0 < m) (hmz : m ≤ z)
    (hR : 0 < R) (hlog : Real.log R ≤ |Real.log z - Real.log m|) : R*m ≤ z := by
  have hz : 0 < z := hm.trans_le hmz
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm hmz)),
    ← Real.log_div hz.ne' hm.ne'] at hlog
  exact (le_div_iff₀ hm).mp ((Real.log_le_log_iff hR (div_pos hz hm)).mp hlog)

theorem log_distance_left_ratio {m z R : ℝ} (hz : 0 < z) (hzm : z ≤ m)
    (hR : 0 < R) (hlog : Real.log R ≤ |Real.log z - Real.log m|) : z ≤ m/R := by
  have hm : 0 < m := hz.trans_le hzm
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hz hzm)), neg_sub,
    ← Real.log_div hm.ne' hz.ne'] at hlog
  have hh := (le_div_iff₀ hz).mp ((Real.log_le_log_iff hR (div_pos hm hz)).mp hlog)
  exact (le_div_iff₀ hR).mpr (by nlinarith)

theorem harmonic_interval_sum67 {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ m ∈ Finset.Icc A B, 1/(m : ℝ)) ≤ 1+Real.log ((B : ℝ)/A) := by
  have ha : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hs := antitone_depth_sum_le hAB (f := fun x => 1/x) (by
    intro x hx y hy hxy
    exact one_div_le_one_div_of_le (ha.trans_le hx.1) hxy)
  rw [integral_one_div_of_pos ha hb] at hs
  exact hs.trans (add_le_add (show 1/(A : ℝ) ≤ 1 from
    (div_le_one ha).mpr (by exact_mod_cast hA)) le_rfl)

/-- A harmonic bound for any finite set of positive integer depths in a
closed real interval. Rounding does not change the ratio in the conclusion. -/
theorem harmonic_real_subset67 (S : Finset ℕ) {A B : ℝ}
    (hA : 1 ≤ A) (hAB : A ≤ B)
    (hS : ∀ m ∈ S, A ≤ (m : ℝ) ∧ (m : ℝ) ≤ B) :
    (∑ m ∈ S, 1/(m : ℝ)) ≤ 1+Real.log (B/A) := by
  have ha : 0 < A := by linarith
  have hb : 0 < B := ha.trans_le hAB
  have hlog : 0 ≤ Real.log (B/A) := Real.log_nonneg ((one_le_div ha).mpr hAB)
  by_cases he : S.Nonempty
  · obtain ⟨m, hm⟩ := he
    have hceil : ⌈A⌉₊ ≤ m := Nat.ceil_le.mpr (hS m hm).1
    have hfloor : m ≤ ⌊B⌋₊ := (Nat.le_floor_iff hb.le).mpr (hS m hm).2
    have hc : 1 ≤ ⌈A⌉₊ := by
      have := Nat.le_ceil A
      by_contra hh
      have hz : ⌈A⌉₊ = 0 := by omega
      rw [hz, Nat.cast_zero] at this
      linarith
    have hcf := hceil.trans hfloor
    have hs : (∑ m ∈ S, 1/(m : ℝ)) ≤
        ∑ m ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, 1/(m : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr (hS j hj).1,
          (Nat.le_floor_iff hb.le).mpr (hS j hj).2⟩
      · intro j hj hnot
        positivity
    apply (hs.trans (harmonic_interval_sum67 hc hcf)).trans
    apply add_le_add le_rfl
    have hcp : (0 : ℝ) < ⌈A⌉₊ := by exact_mod_cast (show 0 < ⌈A⌉₊ by omega)
    have hfp : (0 : ℝ) < ⌊B⌋₊ := by exact_mod_cast (show 0 < ⌊B⌋₊ by omega)
    apply Real.log_le_log (div_pos hfp hcp)
    exact (div_le_div_of_nonneg_right (Nat.floor_le hb.le) hcp.le).trans
      (div_le_div_of_nonneg_left hb.le ha (Nat.le_ceil A))
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [Finset.sum_empty]
    linarith

theorem small_ratio_absorption67 {q R : ℝ} (hq : 0 < q)
    (hR : 1 ≤ R) (hR2 : R ≤ 2) : 1 ≤ (2 : ℝ)^q * R^(-q) := by
  have hp : 0 < R := by linarith
  rw [Real.rpow_neg hp.le]
  rw [← div_eq_mul_inv]
  exact (one_le_div (Real.rpow_pos_of_pos hp q)).mpr
    (Real.rpow_le_rpow hp.le hR2 hq.le)

end Luce.Section6
