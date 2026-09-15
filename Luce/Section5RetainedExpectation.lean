import Luce.Section5RetainedTightness

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Actual cycles retained in S whose unique maximum lies in the deep
shell region. This auxiliary count uses the established maximum-root bijection. -/
def retainedDeepCycleCount {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (S : Finset (Fin n)) (J : ℕ) : ℕ :=
  ((deepShellLabels n J).filter (fun v => v ∈ Section5.maximumCycleRoots R k ∧
    (Function.periodicOrbit (R : Fin n → Fin n) v).toFinset ⊆ S)).card

theorem retainedDeepCycleCount_expectation {n : ℕ} (w : Weights n)
    (k J : ℕ) (S : Finset (Fin n)) :
    (∫ e, (retainedDeepCycleCount (raceRankPermutation e) k S J : ℝ) ∂exponentialRace w) =
      ∑ v ∈ deepShellLabels n J, (exponentialRace w).real (retainedMaximumCycleEvent k S v) := by
  have heq (e : Fin n → ℝ) :
      (retainedDeepCycleCount (raceRankPermutation e) k S J : ℝ) =
        ∑ v ∈ deepShellLabels n J, if e ∈ retainedMaximumCycleEvent k S v then (1 : ℝ) else 0 := by
    simp only [retainedDeepCycleCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, retainedMaximumCycleEvent_eq_actual_roots, Set.mem_setOf_eq]
  have hint (v : Fin n) : Integrable
      (fun e => if e ∈ retainedMaximumCycleEvent k S v then (1 : ℝ) else 0) (exponentialRace w) := by
    convert!
      (integrable_const (μ := exponentialRace w) (1 : ℝ)).indicator
        (measurableSet_retainedMaximumCycleEvent k S v) using 1
  simp_rw [heq]
  rw [integral_finsetSum _ (fun v _ => hint v)]
  apply Finset.sum_congr rfl
  intro v _
  simpa only [Set.indicator_apply, smul_eq_mul, mul_one] using
    integral_indicator_const (μ := exponentialRace w) (1 : ℝ)
      (measurableSet_retainedMaximumCycleEvent k S v)

theorem EndpointShellAssumption.retained_expectation_tightness {w : WeightArray}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J₀ : ℕ, 2 ≤ J₀ ∧ ∀ M δ : ℝ, 0 < δ →
      ∃ J : ℕ, J₀ ≤ J ∧ ∀ᶠ n : ℕ in atTop,
        (∫ e, (retainedDeepCycleCount (raceRankPermutation e) (k+1)
          (retainedCycleLabels (w n) M (1 - Real.exp (-(J₀ : ℝ))/2) δ) J : ℝ)
          ∂exponentialRace (w n)) < ε := by
  simpa only [retainedDeepCycleCount_expectation] using
    hend.retained_maximum_tightness hnorm k hε

end Luce
