import Luce.Section6CriticalRemainingExpectation
import Luce.Section6FastArrivalBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace Luce.Section6

def criticalMissingIndicator {n : ℕ} (k : Fin n) (e : Fin n → ℝ) : ℝ :=
  if k ≤ raceRankPermutation e k then 0 else 1

theorem critical_arrivals_le_rank {n : ℕ} (e : Fin n → ℝ) (i : Fin n) {t : ℝ} (hi : t < e i) :
    criticalArrivalCount t e ≤ ((clockRank e i).val : ℝ) := by
  classical
  rw [critical_arrival_count_card]
  apply Nat.cast_le.mpr
  change (Finset.univ.filter fun j => e j ≤ t).card ≤
    (Finset.univ.filter fun j => e j < e i).card
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.trans_lt hi⟩

/-- Loss of the candidate label is controlled by one clock and the
coarse lower arrival tail. No independence between these events is used. -/
theorem critical_missing_expectation_upper {n : ℕ} (w : Weights n) (k : Fin n)
    {t : ℝ} (ht : 0 ≤ t)
    (hmean : 2*((k.val : ℝ)+1) ≤ (n : ℝ)*populationG w t) :
    (∫ e, criticalMissingIndicator k e ∂exponentialRace w) ≤
      w.rate k*t+Real.exp (-((k.val : ℝ)+1)/8) := by
  classical
  have hn : 0 < n := Nat.zero_lt_of_lt k.isLt
  let bad := {e : Fin n → ℝ | criticalArrivalCount t e ≤ (k.val : ℝ)+1}
  have hbad : MeasurableSet bad := measurableSet_le (criticalArrivalCount_measurable t) measurable_const
  have hM : Integrable (criticalMissingIndicator k) (exponentialRace w) :=
    integrable_race_permutation_statistic w (fun π => if k ≤ π k then 0 else 1)
  have hA := integrable_of_zero_one (exponentialRace w) (measurable_clockArrivalIndicator t k)
    (clockArrivalIndicator_zero_one t k)
  have hB := (integrable_const (1 : ℝ) (μ := exponentialRace w)).indicator hbad
  have hpoint : ∀ᵐ e ∂exponentialRace w, criticalMissingIndicator k e ≤
      clockArrivalIndicator t k e+bad.indicator (fun _ => (1 : ℝ)) e := by
    filter_upwards [exponentialRace_injective_ae w] with e he
    have hA0 : 0 ≤ clockArrivalIndicator t k e := by
      rcases clockArrivalIndicator_zero_one t k e with h | h <;> simp [h]
    have hB0 : 0 ≤ bad.indicator (fun _ => (1 : ℝ)) e := by
      by_cases hb : e ∈ bad <;> simp [hb]
    by_cases hp : k ≤ raceRankPermutation e k
    · simp only [criticalMissingIndicator,if_pos hp]
      positivity
    · simp only [criticalMissingIndicator,if_neg hp]
      by_cases htik : e k ≤ t
      · have heq : clockArrivalIndicator t k e = 1 := by
          simp [clockArrivalIndicator,clockSurvivalIndicator,not_lt.mpr htik]
        rw [heq]
        linarith
      · have hcount := critical_arrivals_le_rank e k (lt_of_not_ge htik)
        rw [raceRankPermutation_eq e he] at hp
        have hrank : (clockRank e k).val < k.val := by exact lt_of_not_ge hp
        have hrankR : ((clockRank e k).val : ℝ) < k.val := by exact_mod_cast hrank
        have hb : e ∈ bad := by change criticalArrivalCount t e ≤ (k.val : ℝ)+1; linarith
        rw [Set.indicator_of_mem hb]
        linarith
  have hi := integral_mono_ae hM (hA.add hB) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add hA hB,integral_clockArrivalIndicator w t ht,
    integral_indicator hbad,integral_const] at hi
  simp only [smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ] at hi
  apply hi.trans
  apply add_le_add _ (critical_arrival_lower_tail w hn ht hmean)
  simpa only [survivalKernel,neg_mul,mul_comm] using
    (one_sub_exp_neg_bounds (mul_nonneg ht (w.positive k).le)).2.2

end Luce.Section6
