import Luce.Section5FactorialPolynomials

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce

def countSieveRemainder {L : ℕ} (q : Fin L → ℕ) (K : ℕ) (x : Fin L → ℕ) : ℝ :=
  (∏ ell, (1 + ((x ell).descFactorial (q ell+(K+1)) : ℝ) /
    (((q ell).factorial : ℝ) * ((K+1).factorial : ℝ)))) - 1

def limitingSieveRemainder {L : ℕ} (q : Fin L → ℕ) (K : ℕ) (rates : Fin L → ℝ) : ℝ :=
  (∏ ell, (1 + rates ell ^ (q ell+(K+1)) /
    (((q ell).factorial : ℝ) * ((K+1).factorial : ℝ)))) - 1

theorem bulk_sieve_remainder_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L K : ℕ) (q : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, countSieveRemainder q K
      (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val)
      ∂exponentialRace (w n)) atTop
      (𝓝 (limitingSieveRemainder q K (fun ell => bulkCycleTraceIntensity f α ell.val))) := by
  classical
  have h := bulk_factorial_polynomial_limit w f hnorm hf L 2
    (fun ell j => if j = 0 then 0 else q ell+(K+1))
    (fun ell j => if j = 0 then 1 else
      1 / (((q ell).factorial : ℝ) * ((K+1).factorial : ℝ))) α hα
  simp [Fin.sum_univ_two, inv_mul_eq_div] at h
  have hr (a b c : ℝ) : a⁻¹ / b * c = c / (a*b) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [hr] at h
  have he (n : ℕ) : (∫ z, countSieveRemainder q K
      (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val)
      ∂exponentialRace (w n)) =
      (∫ z, ∏ ell, (1 + ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial
        (q ell+(K+1)) : ℝ) / (((q ell).factorial : ℝ) * ((K+1).factorial : ℝ)))
        ∂exponentialRace (w n)) - 1 := by
    unfold countSieveRemainder
    rw [integral_sub (integrable_race_permutation_statistic (w n) (fun R =>
      ∏ ell, (1 + ((Section5.bulkCycleCount R α ell.val).descFactorial (q ell+(K+1)) : ℝ) /
        (((q ell).factorial : ℝ) * ((K+1).factorial : ℝ))))) (integrable_const 1)]
    simp
  simp_rw [he]
  exact h.sub_const 1

theorem bulk_sieve_error_integral_le {n : ℕ} (w : Weights n)
    (L K : ℕ) (q : Fin L → ℕ) (α : ℝ) :
    |(∫ z, countVectorSieve q K (fun ell =>
        Section5.bulkCycleCount (raceRankPermutation z) α ell.val) ∂exponentialRace w) -
      (∫ z, (if (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q
        then (1 : ℝ) else 0) ∂exponentialRace w)| ≤
      ∫ z, countSieveRemainder q K (fun ell =>
        Section5.bulkCycleCount (raceRankPermutation z) α ell.val) ∂exponentialRace w := by
  classical
  let A (R : Equiv.Perm (Fin n)) := countVectorSieve q K
    (fun ell => Section5.bulkCycleCount R α ell.val)
  let B (R : Equiv.Perm (Fin n)) : ℝ :=
    if (fun ell => Section5.bulkCycleCount R α ell.val) = q then 1 else 0
  let E (R : Equiv.Perm (Fin n)) := countSieveRemainder q K
    (fun ell => Section5.bulkCycleCount R α ell.val)
  change |(∫ z, A (raceRankPermutation z) ∂exponentialRace w) -
    (∫ z, B (raceRankPermutation z) ∂exponentialRace w)| ≤
      ∫ z, E (raceRankPermutation z) ∂exponentialRace w
  rw [← integral_sub (integrable_race_permutation_statistic w A)
    (integrable_race_permutation_statistic w B)]
  refine abs_integral_le_integral_abs.trans ?_
  apply integral_mono (integrable_race_permutation_statistic w (fun R => |A R-B R|))
    (integrable_race_permutation_statistic w E)
  intro z
  exact countVectorSieve_error q K _

end Luce
