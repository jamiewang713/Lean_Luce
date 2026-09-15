import Luce.Section6DeletedCountRelativeTail
import Luce.Section6RemainingWeightVariance
import Luce.Section5FiniteStatistic

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace Luce.Section6

def criticalArrivalCount {n : ℕ} (t : ℝ) (e : Fin n → ℝ) : ℝ :=
  ∑ i, clockArrivalIndicator t i e

def criticalRemainingWeight {n : ℕ} (w : Weights n) (k : Fin n) (e : Fin n → ℝ) : ℝ :=
  w.total (remaining (raceRankPermutation e).symm k)

theorem critical_arrival_count_card {n : ℕ} (t : ℝ) (e : Fin n → ℝ) :
    criticalArrivalCount t e = ((Finset.univ.filter fun i => e i ≤ t).card : ℝ) := by
  classical
  have he (i : Fin n) : clockArrivalIndicator t i e = if e i ≤ t then (1 : ℝ) else 0 := by
    by_cases hi : e i ≤ t <;> simp [clockArrivalIndicator,clockSurvivalIndicator,hi,not_lt,lt_of_not_ge]
  simp only [criticalArrivalCount,he,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem criticalArrivalCount_measurable {n : ℕ} (t : ℝ) :
    Measurable (criticalArrivalCount (n := n) t) :=
  Finset.measurable_sum _ fun i _ => measurable_clockArrivalIndicator t i

theorem critical_rank_le_arrivals {n : ℕ} (e : Fin n → ℝ) (i : Fin n) {t : ℝ} (hi : e i ≤ t) :
    (raceRank e i : ℝ) ≤ criticalArrivalCount t e := by
  classical
  have hsub : insert i (Finset.univ.filter fun j => e j < e i) ⊆
      Finset.univ.filter (fun j => e j ≤ t) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.le.trans hi⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp)] at hh
  rw [critical_arrival_count_card]
  unfold raceRank
  exact_mod_cast (by omega : 1+(Finset.univ.filter fun j => e j < e i).card ≤
    (Finset.univ.filter fun j => e j ≤ t).card)

theorem critical_remaining_survival_bound {n : ℕ} (w : Weights n) (k : Fin n)
    (e : Fin n → ℝ) (he : Function.Injective e) (t : ℝ)
    (hcount : criticalArrivalCount t e < (k.val : ℝ)+1) :
    criticalRemainingWeight w k e ≤ ∑ i, w.rate i*clockSurvivalIndicator t i e := by
  classical
  have hsurv (i : Fin n) (hi : i ∈ remaining (raceRankPermutation e).symm k) : t < e i := by
    rw [raceRankPermutation_eq e he] at hi
    have hrank : k ≤ rankPermutation e he i := by
      simpa only [remaining,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_symm] using hi
    have hr : k.val+1 ≤ raceRank e i := by
      change k.val ≤ (Finset.univ.filter fun j => e j < e i).card at hrank
      unfold raceRank
      omega
    by_contra hti
    have h := critical_rank_le_arrivals e i (le_of_not_gt hti)
    have h' : (k.val : ℝ)+1 ≤ (raceRank e i : ℝ) := by exact_mod_cast hr
    linarith
  calc
    _ = ∑ i ∈ remaining (raceRankPermutation e).symm k, w.rate i*clockSurvivalIndicator t i e := by
      unfold criticalRemainingWeight Weights.total
      apply Finset.sum_congr rfl
      intro i hi
      simp [clockSurvivalIndicator,hsurv i hi]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ =>
      mul_nonneg (w.positive i).le (by
        rcases clockSurvivalIndicator_zero_one t i e with h | h <;> simp [h]))

theorem critical_arrival_upper_tail {n : ℕ} (w : Weights n) (hn : 0 < n)
    {t m : ℝ} (ht : 0 ≤ t) (hmean : (n : ℝ)*populationG w t ≤ m/2) :
    (exponentialRace w).real {e | m ≤ criticalArrivalCount t e} ≤
      Real.exp (-((Real.log 2-1/2)*m)) := by
  have hm : (∑ i : Fin n, ∫ e, clockArrivalIndicator t i e ∂exponentialRace w) ≤ m/2 := by
    simp_rw [integral_clockArrivalIndicator w t ht]
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
    simpa only [populationG,mul_div_cancel₀ _ hn0] using hmean
  exact bernoulli_upper_tail_of_mean_le_half (exponentialRace w) (clockArrivalIndicator t)
    (measurable_clockArrivalIndicator t) (clockArrivalIndicator_zero_one t)
    (clockArrivalIndicator_independent w t) Finset.univ hm

theorem critical_arrival_lower_tail {n : ℕ} (w : Weights n) (hn : 0 < n)
    {t m : ℝ} (ht : 0 ≤ t) (hmean : 2*m ≤ (n : ℝ)*populationG w t) :
    (exponentialRace w).real {e | criticalArrivalCount t e ≤ m} ≤ Real.exp (-m/8) := by
  have h := (deleted_arrival_relative_tails w hn ∅ ht (eps := 1/2) (by norm_num) (by norm_num)).2
  simp only [deletedG,Finset.sdiff_empty] at h
  change (exponentialRace w).real {e | criticalArrivalCount t e ≤
      (1-(1/2 : ℝ))*((n : ℝ)*populationG w t)} ≤
      Real.exp (-((1/2 : ℝ)^2)*((n : ℝ)*populationG w t)/4) at h
  apply le_trans _ (h.trans _)
  · apply measureReal_mono _ (measure_ne_top _ _)
    intro e he
    change criticalArrivalCount t e ≤ (1-(1/2 : ℝ))*((n : ℝ)*populationG w t)
    exact le_trans he (by linarith)
  · exact Real.exp_le_exp.mpr (by nlinarith)

/-- A deterministic denominator floor plus this coarse first-moment
upper bound suffices for the critical compensator. No variance estimate
or shrinking relative concentration window is needed. -/
theorem critical_remaining_expectation_upper {n : ℕ} (w : Weights n) (k : Fin n)
    {t : ℝ} (ht : 0 ≤ t)
    (hmean : (n : ℝ)*populationG w t ≤ ((k.val : ℝ)+1)/2) :
    (∫ e, criticalRemainingWeight w k e ∂exponentialRace w) ≤
      (n : ℝ)*populationD w 1 t + w.total Finset.univ*
        Real.exp (-((Real.log 2-1/2)*((k.val : ℝ)+1))) := by
  classical
  have hn : 0 < n := Nat.zero_lt_of_lt k.isLt
  let bad := {e : Fin n → ℝ | (k.val : ℝ)+1 ≤ criticalArrivalCount t e}
  have hbad : MeasurableSet bad := measurableSet_le measurable_const (criticalArrivalCount_measurable t)
  let S (e : Fin n → ℝ) := ∑ i, w.rate i*clockSurvivalIndicator t i e
  have hS : Integrable S (exponentialRace w) :=
    integrable_finsetSum _ fun i _ =>
      (integrable_of_zero_one (exponentialRace w) (measurable_clockSurvivalIndicator t i)
        (clockSurvivalIndicator_zero_one t i)).const_mul _
  have hW : Integrable (criticalRemainingWeight w k) (exponentialRace w) :=
    integrable_race_permutation_statistic w (fun π => w.total (remaining π.symm k))
  have hB := (integrable_const (w.total Finset.univ) (μ := exponentialRace w)).indicator hbad
  have hpoint : ∀ᵐ e ∂exponentialRace w, criticalRemainingWeight w k e ≤
      S e+bad.indicator (fun _ => w.total Finset.univ) e := by
    filter_upwards [exponentialRace_injective_ae w] with e he
    by_cases hb : e ∈ bad
    · rw [Set.indicator_of_mem hb]
      have htotal : criticalRemainingWeight w k e ≤ w.total Finset.univ := by
        unfold criticalRemainingWeight Weights.total
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => (w.positive i).le)
      have hs : 0 ≤ S e := Finset.sum_nonneg fun i _ =>
        mul_nonneg (w.positive i).le (by
          rcases clockSurvivalIndicator_zero_one t i e with h | h <;> simp [h])
      linarith
    · rw [Set.indicator_of_notMem hb,add_zero]
      exact critical_remaining_survival_bound w k e he t (lt_of_not_ge hb)
  have hi := integral_mono_ae hW (hS.add hB) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add hS hB,integral_indicator hbad,integral_const] at hi
  have hSm : (∫ e, S e ∂exponentialRace w) = (n : ℝ)*populationD w 1 t := by
    simpa only [S,Finset.sdiff_empty,deletedD,populationD] using deleted_remaining_weight_mean w hn ∅ ht
  rw [hSm] at hi
  apply hi.trans
  simp only [smul_eq_mul,measureReal_def,Measure.restrict_apply_univ]
  exact add_le_add le_rfl (by
    simpa only [mul_comm,measureReal_def,bad] using mul_le_mul_of_nonneg_left
      (critical_arrival_upper_tail w hn ht hmean) (w.total_nonneg Finset.univ))

end Luce.Section6
