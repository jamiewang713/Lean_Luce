import Luce.Section6CriticalReferenceRow

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

def criticalError (n m : ℕ) (eta : ℝ) : ℝ :=
  (1/((m : ℝ)*(Real.log (n : ℝ)-Real.log (m : ℝ))))*
    ((1+Real.log (Real.log (n : ℝ)-Real.log (m : ℝ)))/(Real.log (n : ℝ)-Real.log (m : ℝ))+
      1/(m : ℝ)+((m : ℝ)/n)^eta)

theorem critical_main_block_error_sum {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ K Z delta : ℝ, 0 < K ∧ 2 ≤ Z ∧ 0 < delta ∧ delta < 1 ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n A B : ℕ), 4 ≤ A → A ≤ B → B ≤ n → (n : ℝ) ≤ (A : ℝ)^2 →
      Z ≤ Real.log (n : ℝ)-Real.log (B : ℝ) → (B : ℝ)/(n : ℝ) < delta →
      (∑ k ∈ criticalBlock n A B,
        ∫ e, |predictableChance (w n) (raceRankPermutation e).symm k-
          1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))| ∂exponentialRace (w n)) ≤
        K*(12+1/eta) := by
  obtain ⟨K,Z,delta,hK,hZ,hd,hd1,hpK⟩ := hp.main_probability_approximation
  refine ⟨K,max Z 2,delta,hK,le_max_right _ _,hd,hd1,?_⟩
  intro grid w hw n A B hA hAB hBn hAsq hzB hdelta
  have hA1 : 1 ≤ A := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsum : (∑ k ∈ criticalBlock n A B,
      ∫ e, |predictableChance (w n) (raceRankPermutation e).symm k-
        1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))| ∂exponentialRace (w n)) ≤
      K*(∑ m ∈ Finset.Icc A B, criticalError n m eta) := by
    rw [← critical_block_sum hA1 hBn,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hh := (Finset.mem_filter.mp hk).2
    have hm : (0 : ℝ) < (k.val : ℝ)+1 := by positivity
    have hAm : (A : ℝ) ≤ (k.val : ℝ)+1 := by exact_mod_cast hh.1
    have hmB : (k.val : ℝ)+1 ≤ B := by exact_mod_cast hh.2
    have hb := hpK grid w hw n k (by omega)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) A])
      (((le_max_left _ _).trans hzB).trans (critical_block_log_lower hA1 hk))
      ((div_le_div_of_nonneg_right hmB hn.le).trans_lt hdelta)
    convert hb using 1 <;> first
    | rfl
    | dsimp [criticalError]
      push_cast
      rw [Real.log_div hn.ne' hm.ne']
      ring
  exact hsum.trans (mul_le_mul_of_nonneg_left
    (critical_main_error_sum hp.2.2.2.1 hn hA1 hAB (by exact_mod_cast hBn)
      (by have := (le_max_right _ _).trans hzB; linarith)) hK.le)

end Luce.Section6
