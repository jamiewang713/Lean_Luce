import Luce.Section6CategoryCycleCounting
import Luce.Section5FactorialExpectation

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem integral_category_block_indicator {ι : Type*} [Fintype ι] {n : ℕ}
    (w : Weights n) (k r : ι → ℕ) (t : CategoryCycleVertex k r ↪ Fin n) :
    (∫ e, categoryBlockIndicator (raceRankPermutation e) k r t ∂exponentialRace w) =
      (exponentialRace w).real {e | ∀ x, raceRank e (t x) =
        (t (categoryBlockPermutation k r x)).val+1} := by
  have hset : MeasurableSet {e : Fin n → ℝ | ∀ x, raceRank e (t x) =
      (t (categoryBlockPermutation k r x)).val+1} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro x
    have hm := measurable_clockBeforeCount (fun c : Fin n → ℝ => c)
      (fun c => c (t x)) (fun i => measurable_pi_apply i) (measurable_pi_apply (t x))
    exact measurableSet_eq_fun (hm.const_add 1) measurable_const
  calc
    _ = ∫ e, (if ∀ x, raceRank e (t x) =
        (t (categoryBlockPermutation k r x)).val+1 then (1 : ℝ) else 0)
        ∂exponentialRace w := by
      apply integral_congr_ae
      filter_upwards [exponentialRace_injective_ae w] with e he
      simp only [categoryBlockIndicator, Fintype.prod_boole,
        raceRankPermutation_apply_eq_iff e he]
    _ = _ := by
      simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
        integral_indicator_const (μ := exponentialRace w) (1 : ℝ) hset

/-- The category factorial expectation is a sum of actual rank-cylinder
probabilities, with deterministic restrictions and the exact divisor. -/
theorem category_factorial_expectation_eq_rank_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (w : Weights n) (k r : ι → ℕ) (P : ι → Finset (Fin n) → Prop)
    (hd : ∀ R : Equiv.Perm (Fin n), Pairwise (fun i j =>
      Disjoint (categoryCycleSet R k P i) (categoryCycleSet R k P j))) :
    (∫ e, ∏ i,
      ((categoryCycleSet (raceRankPermutation e) k P i).card.descFactorial (r i) : ℝ)
        ∂exponentialRace w) =
      (∑ t : CategoryCycleVertex k r ↪ Fin n,
        if ∀ b, P b.1 (categoryBlockVertexSet t b) then
          (exponentialRace w).real {e | ∀ x, raceRank e (t x) =
            (t (categoryBlockPermutation k r x)).val+1} else 0) /
        ∏ i, ((k i+1 : ℕ) : ℝ)^r i := by
  have hint (t : CategoryCycleVertex k r ↪ Fin n) : Integrable (fun e =>
      if ∀ b, P b.1 (categoryBlockVertexSet t b) then
        categoryBlockIndicator (raceRankPermutation e) k r t else 0) (exponentialRace w) := by
    by_cases ht : ∀ b, P b.1 (categoryBlockVertexSet t b)
    · simp only [if_pos ht]
      exact integrable_race_permutation_statistic w (fun R => categoryBlockIndicator R k r t)
    · simp only [if_neg ht]
      exact integrable_zero _ _ _
  simp_rw [category_factorial_eq_assignment_sum _ k r P (hd _)]
  rw [integral_div, integral_finsetSum _ (fun t _ => hint t)]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : ∀ b, P b.1 (categoryBlockVertexSet t b)
  · simp only [if_pos ht, integral_category_block_indicator]
  · simp only [if_neg ht, integral_zero]

end Luce.Section6
