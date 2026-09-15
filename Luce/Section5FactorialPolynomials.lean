import Luce.Section5FactorialSieve

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce

/-- Finite products of factorial polynomials converge using only the
proved bulk joint moments. Signed coefficients are allowed. -/
theorem bulk_factorial_polynomial_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L r : ℕ) (p : Fin L → Fin r → ℕ) (c : Fin L → Fin r → ℝ)
    (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, ∏ ell : Fin L, ∑ j : Fin r,
      c ell j * ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial
        (p ell j) : ℝ) ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell : Fin L, ∑ j : Fin r,
        c ell j * bulkCycleTraceIntensity f α ell.val ^ p ell j)) := by
  classical
  have he (n : ℕ) : (∫ z, ∏ ell : Fin L, ∑ j : Fin r,
      c ell j * ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial
        (p ell j) : ℝ) ∂exponentialRace (w n)) =
      ∑ v : Fin L → Fin r, (∏ ell, c ell (v ell)) *
        ∫ z, ∏ ell : Fin L,
          ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial
            (p ell (v ell)) : ℝ) ∂exponentialRace (w n) := by
    simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro v _
      exact integral_const_mul _ _
    · intro v _
      exact integrable_race_permutation_statistic (w n) (fun R =>
        (∏ ell, c ell (v ell)) * ∏ ell,
          ((Section5.bulkCycleCount R α ell.val).descFactorial (p ell (v ell)) : ℝ))
  simp_rw [he]
  rw [Fintype.prod_sum]
  simp_rw [Finset.prod_mul_distrib]
  exact tendsto_finset_sum _ (fun v _ =>
    (bulk_joint_factorial_moments w f hnorm hf L (fun ell => p ell (v ell)) α hα).const_mul _)

/-- The actual joint point-probability sieve has the prescribed limiting
finite exponential expansion. Removing K still requires its error bound. -/
theorem bulk_count_sieve_expectation_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L K : ℕ) (q : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, countVectorSieve q K
      (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val)
      ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell : Fin L, ∑ j : Fin (K+1),
        (-1 : ℝ)^j.val * bulkCycleTraceIntensity f α ell.val ^ (q ell+j.val) /
          (((q ell).factorial : ℝ) * (j.val.factorial : ℝ)))) := by
  have h := bulk_factorial_polynomial_limit w f hnorm hf L (K+1)
    (fun ell j => q ell+j.val)
    (fun ell j => (-1 : ℝ)^j.val / (((q ell).factorial : ℝ) * (j.val.factorial : ℝ))) α hα
  simp only [div_mul_eq_mul_div] at h
  have he (x : Fin L → ℕ) : countVectorSieve q K x =
      ∏ ell : Fin L, ∑ j : Fin (K+1), (-1 : ℝ)^j.val *
        (x ell |>.descFactorial (q ell+j.val) : ℝ) /
          (((q ell).factorial : ℝ) * (j.val.factorial : ℝ)) := by
    unfold countVectorSieve
    apply Finset.prod_congr rfl
    intro ell _
    rw [countSieve_eq_factorial_sum]
    exact (Fin.sum_univ_eq_sum_range _ (K+1)).symm
  simp_rw [he]
  exact h

end Luce
