import Luce.Section3Bernoulli
import Luce.Section6Proposition611
import Luce.Section5Cycles
import Luce.Section6CriticalMissingLabel
import Luce.Section6CriticalLateVertices

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem critical_raceDraw_eq_rank_symm {n : ℕ} (e : Fin n → ℝ) :
    raceDraw e = (raceRankPermutation e).symm := by
  by_cases he : Function.Injective e
  · rw [raceDraw_eq e he,raceRankPermutation_eq e he]
    rfl
  · simp only [raceDraw,raceRankPermutation,he,dite_false]
    rfl

theorem critical_full_probability {n : ℕ} (w : Weights n) (k : Fin n) :
    (raceInteriorBernoulli w 1).probability k =ᵐ[exponentialRace w]
      (fun e => predictableChance w (raceRankPermutation e).symm k) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.isLt)
  have hk : ((k.val : ℝ)+1)/n ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast k.isLt)
  simpa only [if_pos hk,critical_raceDraw_eq_rank_symm] using raceInteriorBernoulli_probability w 1 k

theorem critical_full_observation {n : ℕ} (w : Weights n) (k : Fin n) (e : Fin n → ℝ) :
    (raceInteriorBernoulli w 1).observationReal k e =
      if raceRankPermutation e k = k then (1 : ℝ) else 0 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.isLt)
  have hk : ((k.val : ℝ)+1)/n ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast k.isLt)
  rw [raceInteriorBernoulli_observation,if_pos hk,critical_raceDraw_eq_rank_symm,Equiv.symm_symm]

theorem critical_full_count {n : ℕ} (w : Weights n) (e : Fin n → ℝ) :
    (raceInteriorBernoulli w 1).toProcess.cltCount n e =
      (Section5.cycleCount (raceRankPermutation e) 0 : ℝ) := by
  classical
  rw [FiniteAdaptedBernoulli.toProcess_cltCount,Section5.cycleCount_zero,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [critical_full_observation]
  split_ifs <;> norm_num

theorem critical_predictable_sum_expectation {n : ℕ} (w : Weights n) (S : Finset (Fin n)) :
    (∑ k ∈ S, ∫ e, predictableChance w (raceRankPermutation e).symm k ∂exponentialRace w) =
      ∫ e, (exactCycleVertexCount (raceRankPermutation e) 1 S : ℝ) ∂exponentialRace w := by
  classical
  have hprob (k : Fin n) : (∫ e, predictableChance w (raceRankPermutation e).symm k ∂exponentialRace w) =
      ∫ e, (raceInteriorBernoulli w 1).observationReal k e ∂exponentialRace w := by
    rw [← integral_congr_ae (critical_full_probability w k)]
    rw [integral_congr_ae ((raceInteriorBernoulli w 1).probability_ae_eq_condExp k),integral_condExp]
  simp_rw [hprob]
  rw [← integral_finsetSum _ (fun k _ => (raceInteriorBernoulli w 1).integrable_observationReal k)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro e
  simp only [critical_full_observation,exactCycleVertexCount,Finset.card_filter,Nat.cast_sum,
    Function.minimalPeriod_eq_one_iff_isFixedPt,Function.IsFixedPt]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> norm_num

end Luce.Section6
