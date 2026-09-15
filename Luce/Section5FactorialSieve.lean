import Luce.Section5FactorialMoments
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
open scoped BigOperators
namespace Luce

/-- Finite inclusion-exclusion polynomial for the zero-count event. -/
def zeroCountSieve (K n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), (-1 : ℝ)^j * (n.choose j : ℝ)

theorem zeroCountSieve_succ (K n : ℕ) :
    zeroCountSieve K (n+1) = (-1 : ℝ)^K * (n.choose K : ℝ) := by
  unfold zeroCountSieve
  exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := K))

theorem zeroCountSieve_zero (K : ℕ) : zeroCountSieve K 0 = 1 := by
  unfold zeroCountSieve
  rw [Finset.sum_range_succ']
  simp

/-- The error is bounded by the next binomial moment. No distributional
or moment assumption is used in this pointwise inequality. -/
theorem zeroCountSieve_error (K n : ℕ) :
    |zeroCountSieve K n - (if n = 0 then (1 : ℝ) else 0)| ≤ (n.choose (K+1) : ℝ) := by
  cases n with
  | zero => simp [zeroCountSieve_zero]
  | succ n =>
    rw [zeroCountSieve_succ]
    simp only [Nat.succ_ne_zero, if_false, sub_zero, abs_mul, abs_pow, abs_neg,
      abs_one, one_pow, one_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose K) : (0 : ℝ) ≤ _)]
    exact_mod_cast (show n.choose K ≤ (n+1).choose (K+1) by
      rw [Nat.choose_succ_succ]
      omega)

/-- Finite sieve for an arbitrary count value. -/
def countSieve (q K n : ℕ) : ℝ := (n.choose q : ℝ) * zeroCountSieve K (n-q)

theorem choose_mul_zero_indicator (q n : ℕ) :
    (n.choose q : ℝ) * (if n-q = 0 then 1 else 0) =
      (if n = q then 1 else 0) := by
  by_cases h : n = q
  · subst n; simp
  · by_cases hqn : q ≤ n
    · have hz : n-q ≠ 0 := by omega
      simp [h, hz]
    · simp [Nat.choose_eq_zero_of_lt (by omega : n < q), h]

theorem countSieve_error (q K n : ℕ) :
    |countSieve q K n - (if n = q then (1 : ℝ) else 0)| ≤
      (n.choose q : ℝ) * ((n-q).choose (K+1) : ℝ) := by
  rw [← choose_mul_zero_indicator q n, countSieve, ← mul_sub, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (zeroCountSieve_error K (n-q)) (Nat.cast_nonneg _)

theorem choose_product_eq_factorial_ratio (q j n : ℕ) :
    (n.choose q : ℝ) * ((n-q).choose j : ℝ) =
      (n.descFactorial (q+j) : ℝ) / ((q.factorial : ℝ) * (j.factorial : ℝ)) := by
  have h := Nat.descFactorial_mul_descFactorial (n := n) (k := q) (m := q+j) (by omega)
  simp only [Nat.add_sub_cancel_left] at h
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at h
  have hr : ((j.factorial : ℝ) * ((n-q).choose j : ℝ)) *
      ((q.factorial : ℝ) * (n.choose q : ℝ)) = (n.descFactorial (q+j) : ℝ) := by
    exact_mod_cast h
  apply (eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)))).mpr
  nlinarith [hr]

theorem countSieve_eq_factorial_sum (q K n : ℕ) :
    countSieve q K n = ∑ j ∈ Finset.range (K+1),
      (-1 : ℝ)^j * (n.descFactorial (q+j) : ℝ) /
        ((q.factorial : ℝ) * (j.factorial : ℝ)) := by
  unfold countSieve zeroCountSieve
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_div_assoc, ← choose_product_eq_factorial_ratio q j n]
  ring

theorem countSieve_error_factorial (q K n : ℕ) :
    |countSieve q K n - (if n = q then (1 : ℝ) else 0)| ≤
      (n.descFactorial (q+(K+1)) : ℝ) /
        ((q.factorial : ℝ) * ((K+1).factorial : ℝ)) := by
  simpa only [choose_product_eq_factorial_ratio] using countSieve_error q K n

def countVectorSieve {L : ℕ} (q : Fin L → ℕ) (K : ℕ) (x : Fin L → ℕ) : ℝ :=
  ∏ ell, countSieve (q ell) K (x ell)

/-- A joint point probability is approximated by a finite product of
factorial polynomials. The error involves only higher joint factorial
moments, all of which are already proved for the bulk cycle vector. -/
theorem countVectorSieve_error {L : ℕ} (q : Fin L → ℕ) (K : ℕ) (x : Fin L → ℕ) :
    |countVectorSieve q K x - (if x = q then (1 : ℝ) else 0)| ≤
      (∏ ell, (1 + (x ell |>.descFactorial (q ell+(K+1)) : ℝ) /
        (((q ell).factorial : ℝ) * ((K+1).factorial : ℝ)))) - 1 := by
  classical
  have h := abs_prod_sub_prod_le_envelope (Finset.univ : Finset (Fin L))
    (fun ell => countSieve (q ell) K (x ell))
    (fun ell => if x ell = q ell then (1 : ℝ) else 0)
    (fun _ => (1 : ℝ))
    (fun ell => (x ell |>.descFactorial (q ell+(K+1)) : ℝ) /
      (((q ell).factorial : ℝ) * ((K+1).factorial : ℝ)))
    (fun _ _ => zero_le_one) (fun _ _ => by positivity)
    (fun ell _ => by split_ifs <;> norm_num)
    (fun ell _ => countSieve_error_factorial (q ell) K (x ell))
  have hp : (∏ ell, if x ell = q ell then (1 : ℝ) else 0) =
      (if x = q then 1 else 0) := by
    simp only [Fintype.prod_boole, funext_iff]
    split_ifs <;> rfl
  simpa only [countVectorSieve, hp, Finset.prod_const_one] using h

end Luce
