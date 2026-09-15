import Luce.Endpoint
import Luce.Assumptions

/-! Sharp normalized survivor bound for the shell argument. -/
open scoped BigOperators
namespace Luce

/-- Jensen's bound with coefficient one in logarithmic time. The proof uses
the supporting line `exp x ≥ 1+x`; it requires no bound on individual rates. -/
theorem meanSurvivors_jensen {n : ℕ} (θ : Fin n → ℝ)
    (hsum : ∑ i, θ i = (n : ℝ)) (t : ℝ) :
    (n : ℝ) * Real.exp (-t) ≤ meanSurvivors θ t := by
  have hpoint (i : Fin n) :
      Real.exp (-t) * (1 + (1 - θ i) * t) ≤ Real.exp (-θ i * t) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((1 - θ i) * t))
      (Real.exp_pos (-t)).le
    rw [← Real.exp_add] at h
    convert h using 1 <;> congr 1 <;> ring
  have hsum' : ∑ i : Fin n, (1 + (1 - θ i) * t) = (n : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hsum]
    simp
  calc
    (n : ℝ) * Real.exp (-t) = ∑ i : Fin n, Real.exp (-t) * (1 + (1 - θ i) * t) := by
      rw [← Finset.mul_sum, hsum', mul_comm]
    _ ≤ meanSurvivors θ t := Finset.sum_le_sum fun i _ => hpoint i

theorem NormalizedWeights.meanSurvivors_jensen {w : WeightArray}
    (hnorm : NormalizedWeights w) (n : ℕ) (t : ℝ) :
    (n : ℝ) * Real.exp (-t) ≤ meanSurvivors (w n).rate t := by
  apply Luce.meanSurvivors_jensen
  by_cases hn : n = 0
  · subst n
    simp
  · have h := hnorm n (Nat.pos_of_ne_zero hn)
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp at h
    nlinarith

end Luce
