import Luce.Section6CriticalBernoulliBridge
import Luce.Section6CriticalMainProbability
import Luce.Section6CriticalErrorSums
import Luce.Section6CriticalCutoffs
import Luce.Section6LogExcursionAlgebra

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

def criticalBlock (n A B : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => A ≤ k.val+1 ∧ k.val+1 ≤ B)

theorem critical_block_sum {n A B : ℕ} (hA : 1 ≤ A) (hB : B ≤ n) (f : ℕ → ℝ) :
    (∑ k ∈ criticalBlock n A B, f (k.val+1)) = ∑ m ∈ Finset.Icc A B, f m := by
  classical
  have he : (criticalBlock n A B).image (fun k => k.val+1) = Finset.Icc A B := by
    ext m
    simp only [criticalBlock,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Icc]
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact hk
    · intro hm
      refine ⟨⟨m-1,by omega⟩,?_,?_⟩ <;> dsimp <;> omega
  rw [← he,Finset.sum_image]
  intro i _ j _ hij
  exact Fin.ext (Nat.add_right_cancel hij)

theorem critical_block_log_lower {n A B : ℕ} (hA : 1 ≤ A) {k : Fin n}
    (hk : k ∈ criticalBlock n A B) :
    Real.log (n : ℝ)-Real.log (B : ℝ) ≤ Real.log ((n : ℝ)/((k.val : ℝ)+1)) := by
  have hh := (Finset.mem_filter.mp hk).2
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.isLt)
  have hm : (0 : ℝ) < (k.val : ℝ)+1 := by positivity
  rw [Real.log_div hn.ne' hm.ne']
  exact sub_le_sub_left (Real.log_le_log hm (by exact_mod_cast hh.2)) _

/-- The entire early block is bounded even pathwise. -/
theorem critical_early_sum_bound {n A : ℕ} (hA : 1 ≤ A) (hAn : A ≤ n)
    (hln : 1 ≤ Real.log (n : ℝ))
    (hlogA : Real.log (A : ℝ) ≤ (3/4 : ℝ)*Real.log n)
    {K : ℝ} (hK : 0 ≤ K) {p : Fin n → ℝ}
    (hp : ∀ k ∈ criticalBlock n 1 A,
      p k ≤ K/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))) :
    (∑ k ∈ criticalBlock n 1 A, p k) ≤ 8*K := by
  have hAp : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hn : (0 : ℝ) < n := hAp.trans_le (by exact_mod_cast hAn)
  have hL : 0 < Real.log (n : ℝ)/4 := by linarith
  have hsum : (∑ k ∈ criticalBlock n 1 A, p k) ≤
      (K/(Real.log n/4))*(∑ m ∈ Finset.Icc 1 A, 1/(m : ℝ)) := by
    rw [← critical_block_sum (n := n) (by omega : 1 ≤ 1) hAn,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hm : (0 : ℝ) < (k.val : ℝ)+1 := by positivity
    have hz : Real.log n/4 ≤ Real.log ((n : ℝ)/((k.val : ℝ)+1)) := by
      have := critical_block_log_lower (by omega : 1 ≤ 1) hk
      linarith
    apply (hp k hk).trans
    calc
      _ ≤ K/(((k.val : ℝ)+1)*(Real.log n/4)) :=
        div_le_div_of_nonneg_left hK (mul_pos hm hL) (mul_le_mul_of_nonneg_left hz hm.le)
      _ = _ := by push_cast; field_simp
  have hh := harmonic_interval_sum67 (by omega : 1 ≤ 1) hA
  simp only [Nat.cast_one,div_one] at hh
  have hlog : 1+Real.log (A : ℝ) ≤ 2*Real.log n := by linarith
  calc
    _ ≤ (K/(Real.log n/4))*(2*Real.log n) := hsum.trans
      (mul_le_mul_of_nonneg_left (hh.trans hlog) (div_nonneg hK hL.le))
    _ = _ := by field_simp; ring

theorem critical_block_square_sum {n A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBn : B ≤ n)
    (hzB : 1 ≤ Real.log (n : ℝ)-Real.log (B : ℝ)) :
    (∑ k ∈ criticalBlock n A B,
      (1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1))))^2) ≤ 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ ∑ k ∈ criticalBlock n A B, 1/((k.val : ℝ)+1)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hm : (0 : ℝ) < (k.val : ℝ)+1 := by positivity
      have hz := hzB.trans (critical_block_log_lower hA hk)
      have hq : 1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1))) ≤ 1/((k.val : ℝ)+1) :=
        one_div_le_one_div_of_le hm (by nlinarith)
      have hp : 0 ≤ 1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1))) := by positivity
      simpa only [div_pow,one_pow] using pow_le_pow_left₀ hp hq 2
    _ = ∑ m ∈ Finset.Icc A B, 1/(m : ℝ)^2 := by
      simpa only [Nat.cast_add,Nat.cast_one] using critical_block_sum hA hBn (fun m => 1/(m : ℝ)^2)
    _ ≤ _ := critical_inverse_square_sum hA hAB

end Luce.Section6
