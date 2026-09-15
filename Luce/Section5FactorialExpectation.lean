import Luce.Section5CycleCutoff
import Luce.Section5FiniteStatistic

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

theorem raceRankPermutation_apply_eq_iff {n : ℕ} (e : Fin n → ℝ)
    (he : Function.Injective e) (i j : Fin n) :
    raceRankPermutation e i = j ↔ raceRank e i = j.val+1 := by
  rw [raceRankPermutation_eq e he]
  change clockRank e i = j ↔ raceRank e i = j.val+1
  rw [Fin.ext_iff]
  simp only [clockRank, raceRank, Fin.val_mk]
  omega

theorem integral_cycleBlockIndicator_eq_rank_probability {n : ℕ} (w : Weights n)
    (L : ℕ) (m : Fin L → ℕ) (t : Section5.CycleVertex L m ↪ Fin n) :
    (∫ e, Section5.cycleBlockIndicator (raceRankPermutation e) L m t ∂exponentialRace w) =
      (exponentialRace w).real {e | ∀ x, raceRank e (t x) =
        (t (Section5.cycleBlockPermutation L m x)).val+1} := by
  have hset : MeasurableSet {e : Fin n → ℝ | ∀ x, raceRank e (t x) =
      (t (Section5.cycleBlockPermutation L m x)).val+1} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro x
    have hm := measurable_clockBeforeCount (fun c : Fin n → ℝ => c)
      (fun c => c (t x)) (fun i => measurable_pi_apply i) (measurable_pi_apply (t x))
    exact measurableSet_eq_fun (hm.const_add 1) measurable_const
  calc
    _ = ∫ e, (if ∀ x, raceRank e (t x) =
        (t (Section5.cycleBlockPermutation L m x)).val+1 then (1 : ℝ) else 0)
        ∂exponentialRace w := by
      apply integral_congr_ae
      filter_upwards [exponentialRace_injective_ae w] with e he
      simp only [Section5.cycleBlockIndicator, Fintype.prod_boole,
        raceRankPermutation_apply_eq_iff e he]
    _ = _ := by
      simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
        integral_indicator_const (μ := exponentialRace w) (1 : ℝ) hset

/-- The actual bulk joint factorial expectation equals the sum of rank
cylinder probabilities with exactly the original rotational divisor. -/
theorem bulk_factorial_expectation_eq_rank_sum {n : ℕ} (w : Weights n)
    (L : ℕ) (m : Fin L → ℕ) (α : ℝ) :
    (∫ e, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation e) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace w) =
    (∑ t : Section5.CycleVertex L m ↪ Fin n,
      if ∀ x, ((t x).val : ℝ)+1 ≤ α*n then
        (exponentialRace w).real {e | ∀ x, raceRank e (t x) =
          (t (Section5.cycleBlockPermutation L m x)).val+1} else 0) /
      ∏ ell : Fin L, ((ell.val+1 : ℕ) : ℝ)^m ell := by
  have hint (t : Section5.CycleVertex L m ↪ Fin n) : Integrable (fun e =>
      if ∀ x, ((t x).val : ℝ)+1 ≤ α*n then
        Section5.cycleBlockIndicator (raceRankPermutation e) L m t else 0) (exponentialRace w) := by
    by_cases ht : ∀ x, ((t x).val : ℝ)+1 ≤ α*n
    · simp only [if_pos ht]
      exact integrable_race_permutation_statistic w (fun R => Section5.cycleBlockIndicator R L m t)
    · simp only [if_neg ht]
      exact integrable_zero _ _ _
  simp_rw [Section5.bulk_cycle_factorial_eq_assignment_sum]
  rw [integral_div, integral_finsetSum _ (fun t _ => hint t)]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : ∀ x, ((t x).val : ℝ)+1 ≤ α*n
  · simp only [if_pos ht, integral_cycleBlockIndicator_eq_rank_probability]
  · simp only [if_neg ht, integral_zero]

end Luce
