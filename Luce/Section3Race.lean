import Luce.Section3Mean
import Luce.Section3Profile
import Mathlib.Probability.HasLaw

/-!
# The uniform race estimates under the manuscript's actual assumption

This file assembles `fixed_points.tex:708–726`: small maximal cell mass,
Lipschitz transforms, independent-clock variance, and finite monotone grids.
No convergence of deterministic means or maximal weights is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- Normalization is a standing manuscript hypothesis, not a consequence
silently inserted into `ProfileLimit`. -/
private lemma section3_sum_rates {w : WeightArray} (hnorm : NormalizedWeights w)
    (n : ℕ) : ∑ i, (w (n + 1)).rate i = ((n + 1 : ℕ) : ℝ) := by
  have h := hnorm (n + 1) (Nat.succ_pos n)
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hdiv : (∑ i, (w (n + 1)).rate i) / ((n + 1 : ℕ) : ℝ) = 1 := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h
  simpa only [one_mul] using (div_eq_iff hn).mp hdiv

/-- The unit-mass conclusion stated in Assumption 1.1 (line 228) follows
from normalization and L¹ convergence; it is not a new profile hypothesis. -/
theorem ProfileLimit.integral_eq_one {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) :
    (∫ x, f x ∂profileMeasure) = 1 := by
  have hmass (n : ℕ) : (∫ x, stepProfile w (n + 1) x ∂profileMeasure) = 1 := by
    have h := integral_comp_stepProfile w (n + 1) id rfl
    simp only [id_eq] at h
    rw [h, section3_sum_rates hnorm]
    exact div_self (by positivity)
  have hbound (n : ℕ) : |1 - ∫ x, f x ∂profileMeasure| ≤
      ∫ x, |stepProfile w (n + 1) x - f x| ∂profileMeasure := by
    rw [← hmass n, ← integral_sub (integrable_stepProfile w (n + 1)) hf.integrable]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := profileMeasure)
        (fun x => stepProfile w (n + 1) x - f x))
  have hz : Tendsto (fun _ : ℕ => |1 - ∫ x, f x ∂profileMeasure|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hbound
      (hf.tendsto_integral_abs_sub.comp (tendsto_add_atTop_nat 1))
  have heq : |1 - ∫ x, f x ∂profileMeasure| = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hz
  linarith [abs_eq_zero.mp heq]

/-- Equation `eq:uniform-race`, arrival part. Even normalization is
unnecessary for this part; only the stated L¹ profile assumption is used. -/
theorem section3_uniform_arrival
    (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalArrival clocks t - profileF profileMeasure f t|})
      atTop (𝓝 0) := by
  apply uniform_empiricalArrival
    ((continuousOn_profileF hf.aestronglyMeasurable hf.ae_nonneg).mono
      (fun _ ht => ht.1))
  intro t ht
  simp_rw [meanArrival_eq_profileF w _ ht.1]
  exact ((hf.uniform_profileF T).tendsto_at ht).comp (tendsto_add_atTop_nat 1)

/-- Equation `eq:uniform-race`, with exactly the paper's weak survival
process, including at zero and at arrival times. -/
theorem section3_uniform_remaining
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalRemainingGe (w (n + 1)) clocks t -
          profileD profileMeasure f t|}) atTop (𝓝 0) := by
  apply uniform_empiricalRemainingGe
    ((continuousOn_profileD hf.integrable hf.ae_nonneg).mono (fun _ ht => ht.1))
    (section3_sum_rates hnorm) (rate_le_rowMaxRate w)
    hf.max_weight_div_tendsto_zero
  intro t ht
  simp_rw [meanRemaining_eq_profileD]
  exact (hf.uniform_profileD.tendsto_at ht.1).comp (tendsto_add_atTop_nat 1)

/-- The two uniform process limits in Lemma 3.1 (lines 687–693).
The later quantile and denominator conclusions are separate obligations. -/
theorem section3_uniform_race
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (T : ℝ) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalArrival clocks t - profileF profileMeasure f t|})
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalRemainingGe (w (n + 1)) clocks t -
          profileD profileMeasure f t|}) atTop (𝓝 0)) :=
  ⟨section3_uniform_arrival w f hf T, section3_uniform_remaining w f hnorm hf T⟩

/-- Uniform bad-event estimates transfer to any row spaces having the
prescribed independent exponential clocks. No measurability of an uncountable
supremum is assumed: the outer-measure preimage inequality suffices. -/
theorem section3_uniform_race_of_independent
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Fin (n + 1) → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w (n + 1)).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) (T : ℝ) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalArrival (fun i => E n i ω) t - profileF profileMeasure f t|})
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalRemainingGe (w (n + 1)) (fun i => E n i ω) t -
          profileD profileMeasure f t|}) atTop (𝓝 0)) := by
  have hJoint (n : ℕ) : HasLaw (fun ω i => E n i ω) (exponentialRace (w (n + 1)))
      (P n) := (hIndependent n).hasLaw_pi (hLaw n)
  have hbound (n : ℕ) (s : Set (Fin (n + 1) → ℝ)) :
      P n ((fun ω i => E n i ω) ⁻¹' s) ≤ exponentialRace (w (n + 1)) s := by
    rw [← (hJoint n).map_eq]
    exact Measure.le_map_apply (hJoint n).aemeasurable s
  constructor
  · intro ε hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (section3_uniform_arrival w f hf T ε hε) (fun _ => bot_le) (fun n => hbound n _)
  · intro ε hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (section3_uniform_remaining w f hnorm hf T ε hε) (fun _ => bot_le)
      (fun n => hbound n _)

/-- Equation `eq:uniform-race` with the manuscript's original row index,
on arbitrary probability spaces. The zero row is removed by a proved filter
shift, so no hidden positive-row assumption occurs in the statement. -/
theorem section3_uniform_race_general
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) (T : ℝ) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalArrival (fun i => E n i ω) t - profileF profileMeasure f t|})
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalRemainingGe (w n) (fun i => E n i ω) t -
          profileD profileMeasure f t|}) atTop (𝓝 0)) := by
  have h := section3_uniform_race_of_independent (fun n => Ω (n + 1))
    (fun n => P (n + 1)) w f hnorm hf (fun n => E (n + 1))
    (fun n => hLaw (n + 1)) (fun n => hIndependent (n + 1)) T
  exact ⟨fun ε hε => (tendsto_add_atTop_iff_nat 1).mp (h.1 ε hε),
    fun ε hε => (tendsto_add_atTop_iff_nat 1).mp (h.2 ε hε)⟩

end Luce
