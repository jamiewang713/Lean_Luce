import Luce.Section3Probability

/-!
# The remaining-weight conclusion in the manuscript's notation

This exposes the final assertion of Lemma 3.1 as the total remaining weight
`W_{n,k}/n`, rather than as its proved equal empirical-process representation.
The transfer works on arbitrary row probability spaces carrying the source's
independent exponential clocks and includes the original row index `n`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace Luce

/-- Source Lemma 3.1, equation `eq:uniform-denominator`: the remaining-set
weight converges uniformly to `D(t(k/n))` on every interior window. -/
theorem section3_uniform_remaining_weight_general
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
        ε ≤ |(w n).total (remaining (raceDraw (fun i => E n i ω)) k) / n -
          profileD profileMeasure f
            (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / n))|})
      atTop (𝓝 0) := by
  intro ε hε
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (section3_uniform_denominator w f hnorm hf hα ε hε) (fun _ => bot_le)
  intro n
  have hJoint : HasLaw (fun ω i => E (n + 1) i ω)
      (exponentialRace (w (n + 1))) (P (n + 1)) :=
    (hIndependent (n + 1)).hasLaw_pi (hLaw (n + 1))
  dsimp only
  calc
    P (n + 1) {ω | ∃ k : Fin (n + 1),
        ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ |(w (n + 1)).total
          (remaining (raceDraw (fun i => E (n + 1) i ω)) k) / (n + 1 : ℕ) -
          profileD profileMeasure f
            (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / (n + 1 : ℕ)))|} ≤
      exponentialRace (w (n + 1)) {clocks | ∃ k : Fin (n + 1),
        ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ |(w (n + 1)).total (remaining (raceDraw clocks) k) / (n + 1 : ℕ) -
          profileD profileMeasure f
            (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / (n + 1 : ℕ)))|} := by
      rw [← hJoint.map_eq]
      exact Measure.le_map_apply hJoint.aemeasurable _
    _ ≤ _ := by
      apply measure_mono_ae
      filter_upwards [exponentialRace_injective_ae (w (n + 1))] with clocks hinj
      rintro ⟨k, hk, herr⟩
      refine ⟨k, hk, ?_⟩
      rwa [remaining_weight_eq_empirical (w (n + 1)) clocks hinj k] at herr

end Luce
