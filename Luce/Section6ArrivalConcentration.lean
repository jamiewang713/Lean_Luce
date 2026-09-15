import Luce.Section6BernoulliUpperTail
import Luce.Section6PopulationFinite
import Luce.Section6DeletedOrderMoment
import Luce.EndpointRace

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Arrival by t, including equality; the strict before-count is bounded by it. -/
def clockArrivalIndicator {n : ℕ} (t : ℝ) (i : Fin n) (old : Fin n → ℝ) : ℝ :=
  1-clockSurvivalIndicator t i old

theorem measurable_clockArrivalIndicator {n : ℕ} (t : ℝ) (i : Fin n) :
    Measurable (clockArrivalIndicator t i) :=
  measurable_const.sub (measurable_clockSurvivalIndicator t i)

theorem clockArrivalIndicator_zero_one {n : ℕ} (t : ℝ) (i : Fin n) (old : Fin n → ℝ) :
    clockArrivalIndicator t i old = 0 ∨ clockArrivalIndicator t i old = 1 := by
  rcases clockSurvivalIndicator_zero_one t i old with h | h <;>
    simp [clockArrivalIndicator, h]

theorem clockArrivalIndicator_independent {n : ℕ} (w : Weights n) (t : ℝ) :
    iIndepFun (clockArrivalIndicator t) (exponentialRace w) := by
  exact (clockSurvivalIndicator_independent w t).comp (fun _ => fun x : ℝ => 1-x)
    (fun _ => measurable_const.sub measurable_id)

theorem integral_clockArrivalIndicator {n : ℕ} (w : Weights n) (t : ℝ)
    (ht : 0 ≤ t) (i : Fin n) :
    (∫ old, clockArrivalIndicator t i old ∂exponentialRace w) = 1-survivalKernel t (w.rate i) := by
  unfold clockArrivalIndicator
  rw [integral_sub (integrable_const _) (integrable_of_zero_one (exponentialRace w)
    (measurable_clockSurvivalIndicator t i) (clockSurvivalIndicator_zero_one t i)),
    integral_clockSurvivalIndicator w t ht]
  simp [survivalKernel, mul_comm]

theorem deleted_beforeCount_le_arrivals {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (t : ℝ) :
    (deletedBeforeCount removed old t : ℝ) ≤
      ∑ i ∈ Finset.univ \ removed, clockArrivalIndicator t i old := by
  classical
  simp only [deletedBeforeCount, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : old i < t
  · simp [hi, clockArrivalIndicator, clockSurvivalIndicator, not_lt.mpr hi.le]
  · simp only [if_neg hi, Nat.cast_zero]
    rcases clockArrivalIndicator_zero_one t i old with h | h <;> simp [h]

/-- Concrete exponential-race upper tail. The only helper premise is the
numerical deleted arrival mean bound, still to be discharged by the profile estimates. -/
theorem deleted_before_count_upper_tail {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) {t R : ℝ} (ht : 0 ≤ t)
    (hmean : (n : ℝ)*deletedG w removed t ≤ R/2) :
    (exponentialRace w).real {old | R ≤ (deletedBeforeCount removed old t : ℝ)} ≤
      Real.exp (-((Real.log 2-1/2)*R)) := by
  have hm : (∑ i ∈ Finset.univ \ removed, ∫ old, clockArrivalIndicator t i old ∂exponentialRace w) ≤ R/2 := by
    simp_rw [integral_clockArrivalIndicator w t ht]
    have he : (n : ℝ)*deletedG w removed t =
        ∑ i ∈ Finset.univ \ removed, (1-survivalKernel t (w.rate i)) := by
      unfold deletedG
      field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
    rw [he] at hmean
    exact hmean
  have hb := bernoulli_upper_tail_of_mean_le_half (exponentialRace w) (clockArrivalIndicator t)
    (measurable_clockArrivalIndicator t) (clockArrivalIndicator_zero_one t)
    (clockArrivalIndicator_independent w t) (Finset.univ \ removed) hm
  apply le_trans _ hb
  apply measureReal_mono _ (measure_ne_top _ _)
  intro old ho
  exact ho.trans (deleted_beforeCount_le_arrivals removed old t)

end Luce.Section6
