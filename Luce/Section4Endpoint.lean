import Luce.Section4TailTightness

/-! # Section 4: exact endpoint expectation interfaces

Source: `fixed_points.tex:831–914`. These bridges reuse the finite endpoint
proof and retain both inequalities, the square-root cutoff, and arbitrary
row probability spaces. No profile assumption is needed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- Equation `eq:mean-survivors`, including its expectation interpretation. -/
theorem integral_sum_clockSurvivalIndicator {n : ℕ} (w : Weights n)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ e, ∑ i, clockSurvivalIndicator t i e ∂exponentialRace w) =
      meanSurvivors w.rate t := by
  rw [integral_finsetSum]
  · simp only [integral_clockSurvivalIndicator w t ht, meanSurvivors]
  · intro i _
    apply Integrable.of_bound (measurable_clockSurvivalIndicator t i).aestronglyMeasurable 1
    exact Eventually.of_forall fun e => by
      rcases clockSurvivalIndicator_zero_one t i e with h | h <;> simp [h]

/-- Exact law transfer for the spatial tail expectation, without extra
measurability, integrability or no-ties assumptions on the clocks. -/
theorem tailFixedPointCount_expectation_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (w : Weights n) (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (E i) (expMeasure (w.rate i)) P)
    (hIndependent : iIndepFun E P) (α : ℝ) :
    (∫ ω, (tailFixedPointCount (fun i => E i ω) α : ℝ) ∂P) =
      ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace w := by
  exact (hIndependent.hasLaw_pi hLaw).integral_comp
    (integrable_tailFixedPointCount w α).aestronglyMeasurable

/-- Equation `eq:tail-explicit` with the literal `B = sqrt(n M)`.
The row size is written `n+1` to avoid an artificial nonempty-row hypothesis.
The condition `M ≤ n+1` expresses that these are terminal labels. -/
theorem section4_endpoint_bound {n M : ℕ} (w : Weights (n + 1))
    (hnorm : ∑ i, w.rate i = ((n + 1 : ℕ) : ℝ))
    (hM : 1 ≤ M) (hMn : M ≤ n + 1) {γ s : ℝ} (hγ : 0 < γ)
    (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (terminalCandidate n m))
    (hcut : meanSurvivors w.rate s = Real.sqrt ((n + 1 : ℕ) * (M : ℝ)))
    (hBM : (M : ℝ) ≤ (Real.sqrt ((n + 1 : ℕ) * (M : ℝ)) - 1) / 2)
    (hs : 1 / γ ≤ s) :
    (∫ e, (terminalFixedPointCount (terminalCandidate n) M e : ℝ) ∂exponentialRace w) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) *
        Real.sqrt ((n + 1 : ℕ) * (M : ℝ))) + 2 * Real.exp (-γ * s) ∧
    (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) *
        Real.sqrt ((n + 1 : ℕ) * (M : ℝ))) + 2 * Real.exp (-γ * s) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) *
        Real.sqrt ((n + 1 : ℕ) * (M : ℝ))) +
      2 * (2 * Real.sqrt ((n + 1 : ℕ) * (M : ℝ)) / (n + 1)) ^ (γ / 2) := by
  have hterminal : ∀ m ∈ Finset.Icc 1 M, (terminalCandidate n m).val + m = n + 1 :=
    fun m hm => terminalCandidate_val_add (Finset.mem_Icc.mp hm).1
      ((Finset.mem_Icc.mp hm).2.trans hMn)
  have hBM' : 2 * (M : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) * (M : ℝ)) - 1 := by linarith
  have hs' : 1 ≤ γ * s := by
    have := (div_le_iff₀ hγ).mp hs
    nlinarith
  refine ⟨endpoint_fixedPoint_expectation_bound w _ hM hterminal hγ hrate hcut hBM' hs', ?_⟩
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
    cutoff_exponential_le_rpow (Nat.succ_pos n) w.rate (fun i => (w.positive i).le)
      hnorm (by nlinarith) hcut hγ.le

/-- Equation `eq:tail-epsilon` for the exact spatial tail on arbitrary row
spaces. The same exponent and constant as the manuscript are retained. -/
theorem section4_tail_expectation_bound
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (hnorm : NormalizedWeights w) (hend : EndpointAssumption w)
    (E : (n : ℕ) → Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        limsup (fun n => ∫ ω,
          (tailFixedPointCount (fun i => E n i ω) (1 - ε) : ℝ) ∂P n) atTop ≤
          (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4) := by
  obtain ⟨γ, hγ, δ, hδ, hb⟩ := endpointAssumption_epsilon_estimate w hnorm hend
  refine ⟨γ, hγ, min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro ε hε hεδ
  have heq (n : ℕ) :
      (∫ ω, (tailFixedPointCount (fun i => E (n + 1) i ω) (1 - ε) : ℝ) ∂P (n + 1)) =
        epsilonTailExpectation (fun n => w (n + 1)) ε n := by
    rw [tailFixedPointCount_expectation_eq _ _ _ (hLaw (n + 1)) (hIndependent (n + 1))]
    simp only [tailFixedPointCount_eq_terminalFixedPointCount n _ hε
      (hεδ.trans_le (min_le_right _ _)), epsilonTailExpectation]
  have h := hb ε hε (hεδ.trans_le (min_le_left _ _))
  have hseq : epsilonTailExpectation (fun n => w (n + 1)) ε =
      (fun n => ∫ ω,
        (tailFixedPointCount (fun i => E (n + 1) i ω) (1 - ε) : ℝ) ∂P (n + 1)) :=
    funext fun n => (heq n).symm
  rw [hseq] at h
  rw [← limsup_nat_add (fun n => ∫ ω,
    (tailFixedPointCount (fun i => E n i ω) (1 - ε) : ℝ) ∂P n) 1]
  exact h

end Luce
