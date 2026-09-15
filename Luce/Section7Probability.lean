import Luce.Section7Definitions

/-! # Distribution-free survivor bounds and absence of ties -/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace Luce.Section7
noncomputable section

lemma clockRace_eval {n : ℕ} (g : Fin n → ClockDensity) (i : Fin n) :
    MeasurePreserving (Function.eval i) (clockRace g) (g i).law :=
  measurePreserving_eval _ i

lemma clockRace_independent {n : ℕ} (g : Fin n → ClockDensity) :
    iIndepFun (fun i (e : Fin n → ℝ) => e i) (clockRace g) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

lemma clockRace_collision_zero {n : ℕ} (g : Fin n → ClockDensity)
    {i j : Fin n} (hij : i ≠ j) :
    clockRace g {e | e i = e j} = 0 := by
  have hm := ((clockRace_independent g).indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(clockRace_eval g i).map_eq, (clockRace_eval g j).map_eq] at hm
  have he : {e : Fin n → ℝ | e i = e j} =
      (fun e => (e i, e j)) ⁻¹' Set.diagonal ℝ := rfl
  rw [he, ← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    measurableSet_diagonal, hm, Measure.prod_apply measurableSet_diagonal]
  simp [Set.diagonal]

theorem clockRace_injective_ae {n : ℕ} (g : Fin n → ClockDensity) :
    ∀ᵐ e ∂clockRace g, Function.Injective e := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ => hij
  · have hn : ∀ᵐ e ∂clockRace g, e i ≠ e j := by
      rw [ae_iff]
      simpa only [not_not] using clockRace_collision_zero g hij
    exact hn.mono fun _ hne he => (hne he).elim

lemma otherSurvivors_eq_erase {n : ℕ} (e : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    otherSurvivors e i t = ((survivorSet e t).erase i).card := by
  classical
  simp only [otherSurvivors, survivorSet, Finset.filter_erase]

lemma measurable_survivorProbability {n : ℕ} (g : Fin n → ClockDensity)
    (i : Fin n) (m : ℕ) : Measurable (survivorProbability g i m) :=
  (measurable_measure_prodMk_left (ν := clockRace g)
    ((measurable_otherSurvivors i) (measurableSet_singleton m))).ennreal_toReal

theorem sum_survivorProbability_le_two {n : ℕ} (g : Fin n → ClockDensity)
    (candidate : ℕ → Fin n) (M : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.Icc 1 M, survivorProbability g (candidate m) (m - 1) t) ≤ 2 := by
  simp only [survivorProbability, otherSurvivors_eq_erase]
  apply two_candidate_probability_bound (clockRace g) (fun e => survivorSet e t)
  intro m _
  exact ((measurable_other_survivors (candidate m)).comp
    (measurable_const.prodMk measurable_id)) (measurableSet_singleton _)

lemma survivorMean_antitone {n : ℕ} (g : Fin n → ClockDensity) :
    Antitone (survivorMean g) := by
  intro s t hst
  exact Finset.sum_le_sum fun i _ => measureReal_mono
    (Ioi_subset_Ioi hst) (measure_ne_top _ _)

lemma integral_survivalIndicator {n : ℕ} (g : Fin n → ClockDensity)
    (t : ℝ) (i : Fin n) :
    (∫ e, clockSurvivalIndicator t i e ∂clockRace g) = survival g i t := by
  have hid : clockSurvivalIndicator t i =
      {e : Fin n → ℝ | t < e i}.indicator (fun _ => (1 : ℝ)) := by
    funext e
    simp [clockSurvivalIndicator, Set.indicator_apply]
  rw [hid, integral_indicator_const _
    (measurableSet_lt measurable_const (measurable_pi_apply i))]
  simp only [Measure.real, smul_eq_mul, mul_one, survival]
  exact congrArg ENNReal.toReal
    ((clockRace_eval g i).measure_preimage measurableSet_Ioi.nullMeasurableSet)

lemma mean_other_survivors_lower {n : ℕ} (g : Fin n → ClockDensity)
    (i : Fin n) (t : ℝ) :
    survivorMean g t - 1 ≤ ∑ j ∈ Finset.univ.erase i,
      ∫ e, clockSurvivalIndicator t j e ∂clockRace g := by
  classical
  simp_rw [integral_survivalIndicator]
  have hsum := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
    (fun j => survival g j t) (Finset.mem_univ i)
  have hle : survival g i t ≤ 1 := measureReal_le_one
  dsimp [survivorMean]
  linarith

/-- Chernoff's bound before the cutoff, for arbitrary real clock times. -/
theorem survivorProbability_early {n : ℕ} (g : Fin n → ClockDensity) (i : Fin n)
    {m M : ℕ} {t s B : ℝ} (hmM : m ≤ M) (hM : 1 ≤ M)
    (hts : t ≤ s) (hcut : survivorMean g s = B) (hBM : 2 * (M : ℝ) ≤ B - 1) :
    survivorProbability g i (m - 1) t ≤ Real.exp (-tailConstant * B) := by
  classical
  have hmean := mean_other_survivors_lower g i t
  have hmono := survivorMean_antitone g hts
  rw [hcut] at hmono
  have hmR : ((m - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast (Nat.sub_le m 1).trans hmM
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hind : iIndepFun (clockSurvivalIndicator t) (clockRace g) :=
    (clockRace_independent g).comp
      (fun _ => fun x : ℝ => if t < x then (1 : ℝ) else 0)
      (fun _ => measurable_const.ite (measurableSet_lt measurable_const measurable_id)
        measurable_const)
  have hprob := bernoulli_sum_eq_le_cutoff (clockRace g) (clockSurvivalIndicator t)
    (measurable_clockSurvivalIndicator t) (clockSurvivalIndicator_zero_one t)
    hind (Finset.univ.erase i) (m := ((m - 1 : ℕ) : ℝ)) (B := B)
    (by linarith) (by linarith)
  have hevent : {e : Fin n → ℝ | (∑ j ∈ Finset.univ.erase i,
        clockSurvivalIndicator t j e) = ((m - 1 : ℕ) : ℝ)} =
      {e | otherSurvivors e i t = m - 1} := by
    ext e
    simp only [Set.mem_ofPred_eq, ← other_survivors_eq_sum,
      otherSurvivors_eq_erase, Nat.cast_inj]
  rw [hevent] at hprob
  exact hprob

end
end Luce.Section7
