import Luce.EndpointBlockIntegral
import Luce.EndpointCapacityChernoff
import Luce.EndpointCapacityProbability
import Luce.RankProbability

/-! The concrete block capacity inequality for the actual exponential race.
The early and late premises of the generic integration lemma are proved here. -/
noncomputable section
open Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Luce

theorem capacity_candidate_density_le {n : ℕ} (w : Weights n) (i : Fin n)
    (q : ℕ) {t : ℝ} (ht : 0 < t) :
    w.rate i * Real.exp (-w.rate i * t) * otherSurvivorProbability w i q t ≤
      (w.rate i / (Real.exp (w.rate i * t) - 1)) * fullSurvivorProbability w q t := by
  have h := removed_survivor_probability_le w i q ht.le
  have hd : 0 < 1 - Real.exp (-w.rate i * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [w.positive i]))
  have hp : otherSurvivorProbability w i q t ≤
      fullSurvivorProbability w q t / (1 - Real.exp (-w.rate i * t)) :=
    (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using h)
  calc
    _ ≤ (w.rate i * Real.exp (-w.rate i * t)) *
        (fullSurvivorProbability w q t / (1 - Real.exp (-w.rate i * t))) :=
      mul_le_mul_of_nonneg_left hp (mul_pos (w.positive i) (Real.exp_pos _)).le
    _ = _ := by
      rw [show -w.rate i * t = -(w.rate i * t) by ring, Real.exp_neg]
      have he := (Real.exp_pos (w.rate i * t)).ne'
      have he1 : Real.exp (w.rate i * t) - 1 ≠ 0 :=
        (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos (w.positive i) ht))).ne'
      field_simp

theorem capacity_block_density_le {n : ℕ} (w : Weights (n + 1))
    (block : Finset (Fin (n + 1))) {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hrate : ∀ i ∈ block, a ≤ w.rate i) :
    (∑ i ∈ block, w.rate i * Real.exp (-w.rate i * t) *
      otherSurvivorProbability w i (n - i.val) t) ≤ a / (Real.exp (a * t) - 1) := by
  calc
    _ ≤ ∑ i ∈ block, (a / (Real.exp (a * t) - 1)) *
        fullSurvivorProbability w (n - i.val) t := by
      apply Finset.sum_le_sum
      intro i hi
      apply (capacity_candidate_density_le w i (n - i.val) ht).trans
      apply mul_le_mul_of_nonneg_right
        (capacity_kernel_antitone ht ha (w.positive i) (hrate i hi))
      exact measureReal_nonneg
    _ = (a / (Real.exp (a * t) - 1)) *
        (∑ i ∈ block, fullSurvivorProbability w (n - i.val) t) := by rw [Finset.mul_sum]
    _ ≤ (a / (Real.exp (a * t) - 1)) * 1 :=
      mul_le_mul_of_nonneg_left (sum_fullSurvivorProbability_le_one w block t)
        (div_nonneg ha.le (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_pos ha ht).le)))
    _ = _ := mul_one _

theorem capacity_other_survivor_early {n : ℕ} (w : Weights n) (i : Fin n)
    {q : ℕ} {r s t : ℝ} (hr : 0 ≤ r) (hq : (q : ℝ) ≤ r)
    (hcut : r < meanSurvivors w.rate s - 1) (ht : 0 ≤ t) (hts : t ≤ s) :
    otherSurvivorProbability w i q t ≤
      Real.exp (-((meanSurvivors w.rate s - 1 - r) ^ 2 /
        (2 * (meanSurvivors w.rate s - 1)))) := by
  classical
  have hmean := mean_other_survivors_lower w i ht
  have hm := meanSurvivors_antitone w.rate (fun i => (w.positive i).le) hts
  have hbound := bernoulli_block_lower_tail (exponentialRace w) (clockSurvivalIndicator t)
    (measurable_clockSurvivalIndicator t) (clockSurvivalIndicator_zero_one t)
    (clockSurvivalIndicator_independent w t) (Finset.univ.erase i) hr hcut (by linarith)
  apply le_trans _ hbound
  apply measureReal_mono _ (measure_ne_top _ _)
  intro e he
  change ((survivorSet e t).erase i).card = q at he
  change (∑ j ∈ Finset.univ.erase i, clockSurvivalIndicator t j e) ≤ r
  rw [← other_survivors_eq_sum, he]
  exact hq

/-- `eq:block-endpoint-capacity`, with arbitrary lower/upper bounds on the
block rates and depths. Taking the finite minimum and maximum gives exactly
the manuscript statement. No asymptotic assumption is used. -/
theorem exponentialRace_block_capacity {n : ℕ} (w : Weights (n + 1))
    (block : Finset (Fin (n + 1))) {a r s : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hs : 0 < s)
    (hrate : ∀ i ∈ block, a ≤ w.rate i)
    (hdepth : ∀ i ∈ block, ((n - i.val : ℕ) : ℝ) ≤ r)
    (hcut : r < meanSurvivors w.rate s - 1) :
    (∑ i ∈ block, (exponentialRace w).real {e | raceRank e i = i.val + 1}) ≤
      (block.card : ℝ) * Real.exp (-((meanSurvivors w.rate s - 1 - r) ^ 2 /
        (2 * (meanSurvivors w.rate s - 1)))) + endpointQ (a * s) := by
  simp_rw [fixed_point_probability_integral]
  apply capacity_integral_bound block w.rate (fun i => otherSurvivorProbability w i (n - i.val))
    ha hs (Real.exp_pos _).le hrate
    (fun i _ => measurable_otherSurvivorProbability w i (n - i.val))
    (fun t _ i _ => ⟨otherSurvivorProbability_nonneg w i (n - i.val) t,
      otherSurvivorProbability_le_one w i (n - i.val) t⟩)
  · intro t ht i hi
    exact capacity_other_survivor_early w i hr (hdepth i hi) hcut ht.1.le ht.2
  · intro t ht
    exact capacity_block_density_le w block ha (hs.trans ht) hrate

end Luce
