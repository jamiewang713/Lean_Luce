import Luce.Section5BulkPointProbability
import Luce.Section5IntensityFinite

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce

theorem point_indicator_difference_le_count_difference {L : ℕ}
    (a b q : Fin L → ℕ) (hab : ∀ i, b i ≤ a i) :
    |(if a = q then (1 : ℝ) else 0) - (if b = q then 1 else 0)| ≤
      ∑ i, ((a i-b i : ℕ) : ℝ) := by
  classical
  by_cases h : a = b
  · subst a
    simp
  · have hex : ∃ i, a i ≠ b i := by
      by_contra hn
      apply h
      funext i
      exact Classical.not_not.mp (fun hi => hn ⟨i,hi⟩)
    obtain ⟨i, hi⟩ := hex
    have hn : 1 ≤ a i-b i := by have := hab i; omega
    have hs : (1 : ℝ) ≤ ∑ j, ((a j-b j : ℕ) : ℝ) := by
      have hi : (1 : ℝ) ≤ ((a i-b i : ℕ) : ℝ) := by exact_mod_cast hn
      exact hi.trans (Finset.single_le_sum
        (fun j _ => Nat.cast_nonneg (a j-b j)) (Finset.mem_univ i))
    have hb : |(if a = q then (1 : ℝ) else 0) - (if b = q then 1 else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    exact hb.trans hs

theorem cycle_point_indicator_cutoff_error (w : WeightArray) (L n : ℕ)
    (q : Fin L → ℕ) (α : ℝ) :
    |(∫ z, (if cycleCountVector L (raceRankPermutation z) = q then (1 : ℝ) else 0)
      ∂exponentialRace (w n)) -
      (∫ z, (if (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q
        then (1 : ℝ) else 0) ∂exponentialRace (w n))| ≤
      shortCycleTailExpectation w L n α := by
  classical
  let A (R : Equiv.Perm (Fin n)) : ℝ := if cycleCountVector L R = q then 1 else 0
  let B (R : Equiv.Perm (Fin n)) : ℝ :=
    if (fun ell => Section5.bulkCycleCount R α ell.val) = q then 1 else 0
  change |(∫ z, A (raceRankPermutation z) ∂exponentialRace (w n)) -
    (∫ z, B (raceRankPermutation z) ∂exponentialRace (w n))| ≤ _
  rw [← integral_sub (integrable_race_permutation_statistic (w n) A)
    (integrable_race_permutation_statistic (w n) B), shortCycleTailExpectation_eq_integral]
  refine abs_integral_le_integral_abs.trans ?_
  apply integral_mono (integrable_race_permutation_statistic (w n) (fun R => |A R-B R|))
    (integrable_race_permutation_statistic (w n) (fun R =>
      ∑ ell : Fin L, ((Section5.cycleCount R ell.val - Section5.bulkCycleCount R α ell.val : ℕ) : ℝ)))
  intro z
  exact point_indicator_difference_le_count_difference _ _ q
    (fun ell => bulk_cycle_count_le_total _ ell.val α)

theorem EndpointShellAssumption.cycle_point_formula_tendsto
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) :
    Tendsto (fun α : ℝ => ∏ ell, Real.exp (-bulkCycleTraceIntensity f α ell.val) *
      bulkCycleTraceIntensity f α ell.val ^ q ell / ((q ell).factorial : ℝ))
      (𝓝[<] (1 : ℝ)) (𝓝 (∏ ell, Real.exp (-cycleTraceIntensity f ell.val) *
        cycleTraceIntensity f ell.val ^ q ell / ((q ell).factorial : ℝ))) := by
  apply tendsto_finsetProd
  intro ell _
  have h := hend.bulk_intensity_tendsto hnorm hf ell.val
  exact ((Real.continuous_exp.tendsto _ |>.comp h.neg).mul (h.pow (q ell))).div_const _

end Luce
