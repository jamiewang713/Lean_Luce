import Luce.ExponentialRace
import Luce.EndpointProbability
import Luce.EndpointIntegrals

/-! # Endpoint bounds in the exponential race

The generic Bernoulli and integration estimates are specialized here to the
independent exponential-clock model.
-/

open scoped BigOperators
open Real Set MeasureTheory ProbabilityTheory

namespace Luce

noncomputable section

def clockSurvivalIndicator {n : ℕ} (t : ℝ) (i : Fin n) (clocks : Fin n → ℝ) : ℝ :=
  if t < clocks i then 1 else 0

lemma measurable_clockSurvivalIndicator {n : ℕ} (t : ℝ) (i : Fin n) :
    Measurable (clockSurvivalIndicator t i) := by
  exact measurable_const.ite (measurableSet_lt measurable_const (measurable_pi_apply i))
    measurable_const

lemma clockSurvivalIndicator_zero_one {n : ℕ} (t : ℝ) (i : Fin n)
    (clocks : Fin n → ℝ) :
    clockSurvivalIndicator t i clocks = 0 ∨ clockSurvivalIndicator t i clocks = 1 := by
  simp only [clockSurvivalIndicator]
  split_ifs <;> simp

lemma integral_clockSurvivalIndicator {n : ℕ} (w : Weights n) (t : ℝ)
    (ht : 0 ≤ t) (i : Fin n) :
    (∫ clocks, clockSurvivalIndicator t i clocks ∂exponentialRace w) =
      Real.exp (-w.rate i * t) := by
  have hid : clockSurvivalIndicator t i =
      {clocks : Fin n → ℝ | t < clocks i}.indicator (fun _ => (1 : ℝ)) := by
    funext clocks
    simp [clockSurvivalIndicator, Set.indicator_apply]
  rw [hid, integral_indicator_const _
    (measurableSet_lt measurable_const (measurable_pi_apply i))]
  simp only [Measure.real, smul_eq_mul, mul_one, exponentialRace_survival w i t ht,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, neg_mul]

lemma clockSurvivalIndicator_independent {n : ℕ} (w : Weights n) (t : ℝ) :
    iIndepFun (clockSurvivalIndicator t) (exponentialRace w) := by
  have hind := (exponentialRace_independent w).comp
    (fun _ : Fin n => fun x : ℝ => if t < x then (1 : ℝ) else 0)
    (fun _ => measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const)
  exact hind

lemma other_survivors_eq_sum {n : ℕ} (clocks : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    (((survivorSet clocks t).erase i).card : ℝ) =
      ∑ j ∈ Finset.univ.erase i, clockSurvivalIndicator t j clocks := by
  classical
  simp only [survivorSet, ← Finset.filter_erase, Finset.card_filter, Nat.cast_sum,
    clockSurvivalIndicator]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

lemma measurable_other_survivors {n : ℕ} (i : Fin n) :
    Measurable (fun z : ℝ × (Fin n → ℝ) => ((survivorSet z.2 z.1).erase i).card) := by
  classical
  simp only [survivorSet, ← Finset.filter_erase, Finset.card_filter]
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.ite
    (measurableSet_lt measurable_fst ((measurable_pi_apply j).comp measurable_snd)) measurable_const

/-- Probability that exactly `m` other clocks survive at time `t`. -/
def otherSurvivorProbability {n : ℕ} (w : Weights n) (i : Fin n) (m : ℕ) (t : ℝ) : ℝ :=
  (exponentialRace w).real {clocks | ((survivorSet clocks t).erase i).card = m}

lemma measurable_otherSurvivorProbability {n : ℕ} (w : Weights n) (i : Fin n) (m : ℕ) :
    Measurable (otherSurvivorProbability w i m) := by
  have hset := (measurable_other_survivors i) (measurableSet_singleton m)
  exact (measurable_measure_prodMk_left (ν := exponentialRace w) hset).ennreal_toReal

lemma otherSurvivorProbability_nonneg {n : ℕ} (w : Weights n) (i : Fin n) (m : ℕ) (t : ℝ) :
    0 ≤ otherSurvivorProbability w i m t := ENNReal.toReal_nonneg

lemma otherSurvivorProbability_le_one {n : ℕ} (w : Weights n) (i : Fin n) (m : ℕ) (t : ℝ) :
    otherSurvivorProbability w i m t ≤ 1 := by
  exact measureReal_le_one

lemma sum_otherSurvivorProbability_le_two {n : ℕ} (w : Weights n)
    (candidate : ℕ → Fin n) (M : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.Icc 1 M, otherSurvivorProbability w (candidate m) (m - 1) t) ≤ 2 := by
  apply two_candidate_probability_bound (exponentialRace w) (fun clocks => survivorSet clocks t)
  intro m hm
  exact ((measurable_other_survivors (candidate m)).comp
    (measurable_const.prodMk measurable_id)) (measurableSet_singleton (m - 1))

/-- The expected other-survivor count differs from `S(t)` by at most one. -/
lemma mean_other_survivors_lower {n : ℕ} (w : Weights n) (i : Fin n)
    {t : ℝ} (ht : 0 ≤ t) :
    meanSurvivors w.rate t - 1 ≤
      ∑ j ∈ Finset.univ.erase i,
        ∫ clocks, clockSurvivalIndicator t j clocks ∂exponentialRace w := by
  classical
  simp_rw [integral_clockSurvivalIndicator w t ht]
  have hsum := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
    (fun j => Real.exp (-w.rate j * t)) (Finset.mem_univ i)
  have hexp : Real.exp (-w.rate i * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (w.positive i).le) ht
  dsimp [meanSurvivors]
  linarith

/-- Uniform early-time bound for every terminal candidate. -/
theorem otherSurvivorProbability_early {n : ℕ} (w : Weights n) (i : Fin n)
    {m M : ℕ} {t s B : ℝ} (_hm : 1 ≤ m) (hmM : m ≤ M) (hM : 1 ≤ M)
    (ht : 0 ≤ t) (hts : t ≤ s) (hcut : meanSurvivors w.rate s = B)
    (hBM : 2 * (M : ℝ) ≤ B - 1) :
    otherSurvivorProbability w i (m - 1) t ≤
      Real.exp (-(bernoulliLowerTailConstant / 2) * B) := by
  classical
  have hmean := mean_other_survivors_lower w i ht
  have hmono := meanSurvivors_antitone w.rate (fun j => (w.positive j).le) hts
  rw [hcut] at hmono
  have hmR : ((m - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast (Nat.sub_le m 1).trans hmM
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hprob := bernoulli_sum_eq_le_cutoff (exponentialRace w) (clockSurvivalIndicator t)
    (measurable_clockSurvivalIndicator t) (clockSurvivalIndicator_zero_one t)
    (clockSurvivalIndicator_independent w t) (Finset.univ.erase i)
    (m := ((m - 1 : ℕ) : ℝ)) (B := B) (by linarith) (by linarith)
  have hevent : {clocks : Fin n → ℝ | (∑ j ∈ Finset.univ.erase i,
        clockSurvivalIndicator t j clocks) = ((m - 1 : ℕ) : ℝ)} =
      {clocks | ((survivorSet clocks t).erase i).card = m - 1} := by
    ext clocks
    simp only [Set.mem_ofPred_eq, ← other_survivors_eq_sum, Nat.cast_inj]
  rw [hevent] at hprob
  exact hprob

/-- The endpoint estimate with the candidate probabilities and exponential
clock law fully instantiated. The rank-integral identity converts the left
side into the expected number of terminal fixed points. -/
theorem exponentialRace_endpoint_integrals {n : ℕ} (w : Weights n)
    (candidate : ℕ → Fin n) {M : ℕ} {s B γ : ℝ}
    (hM : 1 ≤ M) (hγ : 0 < γ)
    (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (candidate m))
    (hcut : meanSurvivors w.rate s = B) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hs : 1 ≤ γ * s) :
    (∑ m ∈ Finset.Icc 1 M, ∫ t : ℝ in Ioi 0,
      w.rate (candidate m) * Real.exp (-w.rate (candidate m) * t) *
        otherSurvivorProbability w (candidate m) (m - 1) t) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) * B) +
        2 * Real.exp (-γ * s) := by
  have hbound := endpoint_integral_bound (Finset.Icc 1 M)
    (fun m => w.rate (candidate m)) (fun m => otherSurvivorProbability w (candidate m) (m - 1))
    hγ hs (Real.exp_pos (-(bernoulliLowerTailConstant / 2) * B)).le hrate
    (fun m _ => measurable_otherSurvivorProbability w (candidate m) (m - 1))
    (fun t _ m _ => ⟨otherSurvivorProbability_nonneg w (candidate m) (m - 1) t,
      otherSurvivorProbability_le_one w (candidate m) (m - 1) t⟩)
    (fun t ht m hm => otherSurvivorProbability_early w (candidate m)
      (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2 hM ht.1.le ht.2 hcut hBM)
    (fun t _ => sum_otherSurvivorProbability_le_two w candidate M t)
  simpa using hbound

/-- Normalization gives the second, power-law form of the finite endpoint
bound. -/
theorem exponentialRace_endpoint_integrals_power {n : ℕ} (hn : 0 < n) (w : Weights n)
    (hnorm : ∑ i, w.rate i = (n : ℝ)) (candidate : ℕ → Fin n)
    {M : ℕ} {s B γ : ℝ} (hM : 1 ≤ M) (hγ : 0 < γ)
    (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (candidate m))
    (hcut : meanSurvivors w.rate s = B) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hs : 1 ≤ γ * s) :
    (∑ m ∈ Finset.Icc 1 M, ∫ t : ℝ in Ioi 0,
      w.rate (candidate m) * Real.exp (-w.rate (candidate m) * t) *
        otherSurvivorProbability w (candidate m) (m - 1) t) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) * B) +
        2 * (2 * B / n) ^ (γ / 2) := by
  apply (exponentialRace_endpoint_integrals w candidate hM hγ hrate hcut hBM hs).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact cutoff_exponential_le_rpow hn w.rate (fun i => (w.positive i).le) hnorm
    (by nlinarith) hcut hγ.le

end

end Luce
