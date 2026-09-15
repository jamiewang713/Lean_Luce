import Luce.Section6Lemma67
import Luce.Section5FiniteStatistic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Luce.Section6

/-- All counts here are integrable because they are statistics of a finite
permutation. Summing lengths therefore sums their actual expectations. -/
theorem sum_cycle_expectations67 {n : ℕ} (w : Weights n) (L : ℕ)
    (F : Fin L → Equiv.Perm (Fin n) → ℕ) {C : ℝ}
    (h : ∀ k, (∫ clocks, (F k (raceRankPermutation clocks) : ℝ)
      ∂exponentialRace w) ≤ C) :
    (∫ clocks, ((∑ k, F k (raceRankPermutation clocks) : ℕ) : ℝ)
      ∂exponentialRace w) ≤ (L : ℝ)*C := by
  simp_rw [Nat.cast_sum]
  rw [integral_finsetSum _ (fun k _ =>
    integrable_race_permutation_statistic w (fun p => (F k p : ℝ)))]
  exact (Finset.sum_le_sum (fun k _ => h k)).trans_eq (by simp)

/-- The two excursion estimates also hold for the total number of cycles
of all lengths 1,...,L, with one constant and exponent for both corners. -/
theorem lemma67_excursion_totals (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (L : ℕ) :
    ∃ C delta q : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < q ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ side : Corner, (cornerBehavior left right side).active →
    ∀ (n : ℕ) (A B : ℝ), 1 ≤ A → A ≤ B → B/(n : ℝ) ≤ delta →
    (∫ clocks, ((∑ k : Fin L,
      intervalDiscardedCycleCount (raceRankPermutation clocks) side k.val A B : ℕ) : ℝ)
      ∂exponentialRace (w n)) ≤ C ∧
    ∀ R : ℝ, 1 ≤ R →
      (∫ clocks, ((∑ k : Fin L,
        logarithmicExcursionCount (raceRankPermutation clocks) side k.val A B R : ℕ) : ℝ)
        ∂exponentialRace (w n)) ≤ C*(1+Real.log (B/A))*R^(-q) := by
  obtain ⟨C, d, q, hC, hd, hd1, hq, hb⟩ := lemma67_active f left right hp L
  refine ⟨((L : ℝ)+1)*C, d, q, by positivity, hd, hd1, hq, ?_⟩
  intro grid w hw side ha n A B hA hAB hB
  constructor
  · have hs := sum_cycle_expectations67 (w n) L
      (fun k p => intervalDiscardedCycleCount p side k.val A B)
      (fun k => (hb k.val k.isLt side ha grid w hw).2.1 n A B hA hAB hB)
    exact hs.trans (by nlinarith)
  · intro R hR
    have hs := sum_cycle_expectations67 (w n) L
      (fun k p => logarithmicExcursionCount p side k.val A B R)
      (fun k => (hb k.val k.isLt side ha grid w hw).2.2 n A B R hA hAB hB hR)
    have ha0 : 0 < A := by linarith
    have hlog : 0 ≤ 1+Real.log (B/A) := by
      have := Real.log_nonneg ((one_le_div ha0).mpr hAB)
      linarith
    have ht : 0 ≤ C*(1+Real.log (B/A))*R^(-q) := by positivity
    apply hs.trans
    nlinarith

theorem lemma67_regular_totals (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (L : ℕ) {eps : ℝ}
    (he : 0 < eps) (he1 : eps < 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ,
      (∫ clocks, ((∑ k : Fin L, selectedRootCycleCount (raceRankPermutation clocks) k.val
        (offActiveLabels left right n eps) : ℕ) : ℝ) ∂exponentialRace (w n)) ≤ C := by
  obtain ⟨C, hC, hb⟩ := lemma67_regular f left right hp L eps he he1
  refine ⟨((L : ℝ)+1)*C, by positivity, ?_⟩
  intro grid w hw n
  have hs := sum_cycle_expectations67 (w n) L
    (fun k p => selectedRootCycleCount p k.val (offActiveLabels left right n eps))
    (fun k => hb grid w hw n k.val k.isLt)
  exact hs.trans (by nlinarith)

end Luce.Section6
