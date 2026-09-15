import Luce.Section4TailCountIndex
import Luce.Section4TailProbability
import Luce.Section4TailAssumptions
import Luce.Section4TailLimit

/-! # Tail tightness in Section 4

Source: `fixed_points.tex`, equation `eq:tail-tightness`.
The user approved this exact count and statement, recorded in
`proposals/Section4TailTightness.lean`. Probability spaces may vary with the
row. Independence is required only within each row. No profile convergence,
extra integrability, or no-ties hypothesis is used.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

universe u

namespace Luce

/-- Markov's inequality for the exact spatial tail, expressed using the
existing terminal expectation. The joint law is derived from the approved
clock hypotheses. -/
lemma tail_probability_le_epsilonTailExpectation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (w : WeightArray) (n : ℕ) (E : Fin (n + 1) → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (E i) (expMeasure ((w (n + 1)).rate i)) P)
    (hIndependent : iIndepFun E P) {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    P.real {ω | 0 < tailFixedPointCount (fun i => E i ω) (1 - ε)} ≤
      epsilonTailExpectation (fun n => w (n + 1)) ε n := by
  rw [tailFixedPointCount_probability_eq P (w (n + 1)) E hLaw hIndependent]
  have h := tailFixedPointCount_probability_le_expectation (w (n + 1)) (1 - ε)
  simpa only [tailFixedPointCount_eq_terminalFixedPointCount n _ hε hεone,
    epsilonTailExpectation] using h

/-- The approved general-space form of `eq:tail-tightness`.
The constants in `EndpointAssumption` remain uniform in row size and label. -/
theorem tail_fixed_point_tightness
    (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray)
    (hnorm : NormalizedWeights w) (hend : EndpointAssumption w)
    (E : (n : ℕ) → Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) :
    Tendsto
      (fun α : ℝ => limsup
        (fun n : ℕ => (P n).real
          {ω | 0 < tailFixedPointCount (fun i => E n i ω) α}) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let p (α : ℝ) (n : ℕ) : ℝ :=
    (P n).real {ω | 0 < tailFixedPointCount (fun i => E n i ω) α}
  have hp_nonneg (α : ℝ) (n : ℕ) : 0 ≤ p α n := measureReal_nonneg
  have hp_bounded (α : ℝ) : IsBoundedUnder (· ≤ ·) atTop (p α) :=
    ⟨1, show ∀ᶠ n : ℕ in atTop, p α n ≤ 1 from
      Eventually.of_forall fun n => measureReal_le_one⟩
  have hlim_nonneg (α : ℝ) : 0 ≤ limsup (p α) atTop :=
    le_limsup_of_frequently_le (Eventually.of_forall (hp_nonneg α)).frequently (hp_bounded α)
  obtain ⟨γ, hγ, δ, hδ, hestimate⟩ :=
    endpointAssumption_epsilon_estimate_bounded w hnorm hend
  apply tendsto_zero_of_endpoint_power_bound (fun α => limsup (p α) atTop)
    hlim_nonneg hγ (lt_min hδ (by norm_num : (0 : ℝ) < 1))
  intro ε hε hεδ
  have hεone : ε < 1 := hεδ.trans_le (min_le_right _ _)
  obtain ⟨hbounded, hpower⟩ := hestimate ε hε (hεδ.trans_le (min_le_left _ _))
  have hcomparison : (fun n : ℕ => p (1 - ε) (n + 1)) ≤ᶠ[atTop]
      epsilonTailExpectation (fun n => w (n + 1)) ε :=
    Eventually.of_forall fun n => tail_probability_le_epsilonTailExpectation
      (P (n + 1)) w n (E (n + 1)) (hLaw (n + 1)) (hIndependent (n + 1)) hε hεone
  have hlim := limsup_le_limsup hcomparison
    (isCoboundedUnder_le_of_le atTop (fun n => hp_nonneg (1 - ε) (n + 1))) hbounded
  rw [limsup_nat_add] at hlim
  exact hlim.trans hpower

end Luce
