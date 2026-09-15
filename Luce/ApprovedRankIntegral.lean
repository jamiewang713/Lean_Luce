import Luce.RankProbability
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Approved pilot: the rank integral

Source: `fixed_points.tex`, Lemma `lem:rank-integral`, equation
`eq:rank-integral` (Section 4).

The user approved the statement and definitions below on 2026-09-10.
The target is on an arbitrary probability space with independent exponential
clocks. `Fin n` label `k` represents the paper's label `k.val + 1`.
No integrability or no-ties assumptions may be added to the target.
-/

open MeasureTheory ProbabilityTheory

namespace Luce

/-- Approved definition: one plus the number of other clocks ringing earlier. -/
noncomputable def rankOf {n : ℕ}
    (e : Fin n → ℝ) (k : Fin n) : ℕ := by
  classical
  exact 1 +
    ((Finset.univ.erase k).filter
      (fun j => e j < e k)).card

/-- Approved definition: the number of other clocks surviving strictly past `t`. -/
noncomputable def otherSurvivors {n : ℕ}
    (e : Fin n → ℝ) (k : Fin n) (t : ℝ) : ℕ := by
  classical
  exact ((Finset.univ.erase k).filter
    (fun j => t < e j)).card

private lemma rankOf_eq_raceRank {n : ℕ} (e : Fin n → ℝ) (k : Fin n) :
    rankOf e k = raceRank e k := by
  classical
  simp only [rankOf, raceRank, Finset.filter_erase]
  rw [Finset.erase_eq_of_notMem (by simp)]

private lemma otherSurvivors_eq {n : ℕ} (e : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    otherSurvivors e k t = ((survivorSet e t).erase k).card := by
  classical
  simp only [otherSurvivors, survivorSet, Finset.filter_erase]

/-- The rank event is measurable as a predicate on a finite clock vector. -/
lemma measurable_rankOf {n : ℕ} (k : Fin n) :
    Measurable (fun e : Fin n → ℝ => rankOf e k) := by
  classical
  simp only [rankOf, Finset.card_filter]
  apply measurable_const.add
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.ite
    (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply k)) measurable_const

/-- Joint measurability in the deterministic time and the finite clock vector. -/
lemma measurable_otherSurvivors {n : ℕ} (k : Fin n) :
    Measurable (fun z : ℝ × (Fin n → ℝ) => otherSurvivors z.2 k z.1) := by
  classical
  simp only [otherSurvivors, Finset.card_filter]
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.ite
    (measurableSet_lt measurable_fst ((measurable_pi_apply j).comp measurable_snd))
    measurable_const

private lemma measurable_otherSurvivors_at {n : ℕ} (k : Fin n) (t : ℝ) :
    Measurable (fun e : Fin n → ℝ => otherSurvivors e k t) :=
  (measurable_otherSurvivors k).comp (measurable_const.prodMk measurable_id)

private lemma measurable_survivorProbability_product {n : ℕ}
    (w : Weights n) (k : Fin n) (m : ℕ) :
    Measurable (fun t : ℝ => (exponentialRace w).real
      {e | otherSurvivors e k t = m}) := by
  have hs : MeasurableSet {z : ℝ × (Fin n → ℝ) | otherSurvivors z.2 k z.1 = m} :=
    (measurable_otherSurvivors k) (measurableSet_singleton m)
  have hm := measurable_measure_prodMk_left (ν := exponentialRace w) hs
  exact hm.ennreal_toReal

/-- The survivor-count probability is measurable in time, derived from the
approved clock hypotheses rather than assumed in the rank integral. -/
lemma measurable_survivorProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i)
    (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (E i) (expMeasure (θ i)) P)
    (hIndependent : iIndepFun E P) (k : Fin n) (m : ℕ) :
    Measurable (fun t : ℝ => P.real
      {ω | otherSurvivors (fun i => E i ω) k t = m}) := by
  let w : Weights n := ⟨θ, hθ⟩
  have hJoint : HasLaw (fun ω i => E i ω) (exponentialRace w) P :=
    hIndependent.hasLaw_pi hLaw
  have hprob (t : ℝ) : P.real {ω | otherSurvivors (fun i => E i ω) k t = m} =
      (exponentialRace w).real {e | otherSurvivors e k t = m} :=
    hJoint.measureReal_eq ((measurable_otherSurvivors_at k t) (measurableSet_singleton m))
  simp_rw [hprob]
  exact measurable_survivorProbability_product w k m

/-- Integrability of the exact approved integrand. Its absolute value is
bounded by the exponential density, whose integrability follows from `hθ`.
This obligation is discharged without adding a hypothesis to `rank_integral`. -/
theorem rank_integrand_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i)
    (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (E i) (expMeasure (θ i)) P)
    (hIndependent : iIndepFun E P) (k : Fin n) :
    IntegrableOn (fun t : ℝ =>
      θ k * Real.exp (-(θ k * t)) *
        P.real {ω | otherSurvivors (fun i => E i ω) k t = n - (k.val + 1)})
      (Set.Ioi 0) := by
  have hprob := measurable_survivorProbability P n θ hθ E hLaw hIndependent k
    (n - (k.val + 1))
  have hdensity : IntegrableOn (fun t : ℝ => θ k * Real.exp (-(θ k * t)))
      (Set.Ioi 0) := by
    simpa only [IntegrableOn, neg_mul] using
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos (hθ k)) (0 : ℝ)).const_mul (θ k)
  apply hdensity.mono'
    (((measurable_id.const_mul (θ k)).neg.exp.const_mul (θ k)).mul hprob).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have hp0 : 0 ≤ P.real {ω | otherSurvivors (fun i => E i ω) k t = n - (k.val + 1)} :=
    measureReal_nonneg
  have hp1 : P.real {ω | otherSurvivors (fun i => E i ω) k t = n - (k.val + 1)} ≤ 1 :=
    measureReal_le_one
  change ‖θ k * Real.exp (-(θ k * t)) *
    P.real {ω | otherSurvivors (fun i => E i ω) k t = n - (k.val + 1)}‖ ≤
      θ k * Real.exp (-(θ k * t))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (mul_nonneg (hθ k).le (Real.exp_pos _).le) hp0)]
  exact mul_le_of_le_one_right (mul_nonneg (hθ k).le (Real.exp_pos _).le) hp1

/-- **Locked statement:** `fixed_points.tex`, Lemma `lem:rank-integral`,
equation `eq:rank-integral`. Approved by the user before this proof was written.
The probability space is arbitrary and both probabilities use the same `P`.
-/
theorem rank_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (n : ℕ)
    (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i)
    (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i,
      ProbabilityTheory.HasLaw
        (E i) (ProbabilityTheory.expMeasure (θ i)) P)
    (hIndependent : ProbabilityTheory.iIndepFun E P)
    (k : Fin n) :
    P.real {ω | rankOf (fun i => E i ω) k = k.val + 1}
      =
    ∫ t in Set.Ioi (0 : ℝ),
      θ k * Real.exp (-(θ k * t)) *
        P.real {ω |
          otherSurvivors (fun i => E i ω) k t
            = n - (k.val + 1)} := by
  classical
  cases n with
  | zero => exact Fin.elim0 k
  | succ n =>
    let w : Weights (n + 1) := ⟨θ, hθ⟩
    have hJoint : HasLaw (fun ω i => E i ω) (exponentialRace w) P :=
      hIndependent.hasLaw_pi hLaw
    have hprob (t : ℝ) :
        P.real {ω | otherSurvivors (fun i => E i ω) k t = n + 1 - (k.val + 1)} =
          (exponentialRace w).real {e | otherSurvivors e k t = n + 1 - (k.val + 1)} :=
      hJoint.measureReal_eq ((measurable_otherSurvivors_at k t)
        (measurableSet_singleton _))
    calc
      _ = (exponentialRace w).real {e | rankOf e k = k.val + 1} :=
        hJoint.measureReal_eq ((measurable_rankOf k) (measurableSet_singleton _))
      _ = ∫ t in Set.Ioi (0 : ℝ), θ k * Real.exp (-(θ k * t)) *
          (exponentialRace w).real {e | otherSurvivors e k t = n + 1 - (k.val + 1)} := by
        simpa only [rankOf_eq_raceRank, otherSurvivors_eq, Nat.add_sub_add_right, neg_mul]
          using fixed_point_probability_integral w k
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        dsimp only
        rw [hprob]

end Luce
