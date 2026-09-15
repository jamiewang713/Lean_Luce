import Luce.Section4EndpointRace
import Luce.Section4EndpointCapacityAnalytic

noncomputable section
open Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Luce

def fullSurvivorProbability {n : ℕ} (w : Weights n) (q : ℕ) (t : ℝ) : ℝ :=
  (exponentialRace w).real {e | (∑ i, clockSurvivalIndicator t i e) = (q : ℝ)}

/-- Removing a candidate costs its probability of already having rung.
Independence is proved from the canonical exponential product measure. -/
theorem removed_survivor_probability_le {n : ℕ} (w : Weights n) (i : Fin n)
    (q : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 - Real.exp (-w.rate i * t)) * otherSurvivorProbability w i q t ≤
      fullSurvivorProbability w q t := by
  classical
  let Y : (Fin n → ℝ) → ℝ := fun e =>
    ∑ j ∈ Finset.univ.erase i, clockSurvivalIndicator t j e
  let Z : (Fin n → ℝ) → ℝ := clockSurvivalIndicator t i
  have hind : IndepFun Y Z (exponentialRace w) :=
    (by
      convert! (clockSurvivalIndicator_independent w t).indepFun_finsetSum_of_notMem
        (measurable_clockSurvivalIndicator t) (s := Finset.univ.erase i) (i := i)
        (by simp) using 1
      funext e
      simp [Y])
  have he := hind.measure_inter_preimage_eq_mul { (q : ℝ) } { (0 : ℝ) }
    (measurableSet_singleton _) (measurableSet_singleton _)
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_mul] at her
  have hY : {e | Y e = (q : ℝ)} =
      {e | ((survivorSet e t).erase i).card = q} := by
    ext e
    simp only [Y, mem_ofPred_eq, ← other_survivors_eq_sum, Nat.cast_inj]
  have hZ : {e | Z e = 0} = {e : Fin n → ℝ | t < e i}ᶜ := by
    ext e
    simp [Z, clockSurvivalIndicator]
  have hZprob : (exponentialRace w).real {e | Z e = 0} =
      1 - Real.exp (-w.rate i * t) := by
    rw [hZ, measureReal_compl (measurableSet_lt measurable_const (measurable_pi_apply i))]
    simp only [Measure.real, exponentialRace_survival w i t ht,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, neg_mul, measure_univ, ENNReal.toReal_one]
  have hsubset : (Y ⁻¹' {(q : ℝ)}) ∩ (Z ⁻¹' {(0 : ℝ)}) ⊆
      {e | (∑ j, clockSurvivalIndicator t j e) = (q : ℝ)} := by
    intro e he
    have hy : Y e = (q : ℝ) := he.1
    have hz : Z e = 0 := he.2
    have hs := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
      (fun j => clockSurvivalIndicator t j e) (Finset.mem_univ i)
    change Y e + Z e = _ at hs
    change _ = _
    linarith
  have hle := measureReal_mono hsubset (measure_ne_top (exponentialRace w) _)
  change (exponentialRace w).real ((Y ⁻¹' {(q : ℝ)}) ∩ (Z ⁻¹' {(0 : ℝ)})) =
    (exponentialRace w).real {e | Y e = (q : ℝ)} *
      (exponentialRace w).real {e | Z e = 0} at her
  rw [her, hZprob, hY] at hle
  simpa only [otherSurvivorProbability, fullSurvivorProbability, mul_comm] using hle

theorem sum_fullSurvivorProbability_le_one {n : ℕ} (w : Weights (n + 1))
    (s : Finset (Fin (n + 1))) (t : ℝ) :
    ∑ i ∈ s, fullSurvivorProbability w (n - i.val) t ≤ 1 := by
  classical
  let A (i : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) :=
    {e | (∑ j, clockSurvivalIndicator t j e) = ((n - i.val : ℕ) : ℝ)}
  have hm (i : Fin (n + 1)) : MeasurableSet (A i) :=
    (Finset.measurable_sum _ (fun j _ => measurable_clockSurvivalIndicator t j))
      (measurableSet_singleton _)
  have hd : Set.Pairwise (s : Set (Fin (n + 1)))
      (fun i j => AEDisjoint (exponentialRace w) (A i) (A j)) := by
    intro i _ j _ hij
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro e hi hj
    have he : n - i.val = n - j.val := by
      apply Nat.cast_injective (R := ℝ)
      exact hi.symm.trans hj
    apply hij
    apply Fin.ext
    omega
  have h := sum_measure_le_measure_univ (μ := exponentialRace w)
    (fun i (_ : i ∈ s) => (hm i).nullMeasurableSet) hd
  have hr := ENNReal.toReal_mono (measure_ne_top (exponentialRace w) _) h
  simpa only [ENNReal.toReal_sum (fun i (_ : i ∈ s) => measure_ne_top (exponentialRace w) (A i)),
    measure_univ, ENNReal.toReal_one, fullSurvivorProbability, Measure.real, A] using hr

end Luce
