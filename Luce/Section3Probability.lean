import Luce.Section3OrderStats

/-!
# The actual predictable ratio in the interior

Source: `fixed_points.tex:569–578, 681–684, 751–758, 799–805`.
The draw permutation is obtained by sorting the clocks, with an arbitrary
identity extension on the null event of ties. The original strictly positive
weights make every remaining-set denominator positive.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- Total extension of the draw order to the null event of tied clocks. -/
def raceDraw {n : ℕ} (clocks : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  if h : Function.Injective clocks then drawPermutation clocks h else Equiv.refl _

lemma raceDraw_eq {n : ℕ} (clocks : Fin n → ℝ) (h : Function.Injective clocks) :
    raceDraw clocks = drawPermutation clocks h := by simp [raceDraw, h]

/-- The normalized remaining weight is exactly the weak empirical rate
evaluated at the arrival, including the arriving label itself. -/
theorem remaining_weight_eq_empirical {n : ℕ} (w : Weights n)
    (clocks : Fin n → ℝ) (hinj : Function.Injective clocks) (k : Fin n) :
    w.total (remaining (raceDraw clocks) k) / n =
      empiricalRemainingGe w clocks (orderTime clocks k) := by
  classical
  rw [raceDraw_eq clocks hinj, remaining_eq_clock_survivors,
    orderTime_eq_arrivalTime clocks hinj]
  simp [Weights.total, empiricalRemainingGe, Finset.sum_filter]

/-- The compact-interval denominator lower bound in line 752. It follows
from positivity of D and monotonicity of both D and the inverse time. -/
theorem section3_denominator_lower {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < profileD profileMeasure f (profileQuantile profileMeasure f α) ∧
      ∀ x ∈ Icc (0 : ℝ) α,
        profileD profileMeasure f (profileQuantile profileMeasure f α) ≤
          profileD profileMeasure f (profileQuantile profileMeasure f x) := by
  have hqa := profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hα0, hα1⟩
  refine ⟨profileD_pos hf.integrable hf.ae_pos hqa, ?_⟩
  intro x hx
  have hxx : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1, hx.2.trans_lt hα1⟩
  exact antitoneOn_profileD hf.integrable hf.ae_nonneg
    (profileQuantile_nonneg hf.integrable hf.ae_pos hxx) hqa
    ((strictMonoOn_profileQuantile hf.integrable hf.ae_pos).monotoneOn
      hxx ⟨hα0, hα1⟩ hx.2)

/-- The pointwise bound of lines 802–803 on the good denominator event. -/
theorem race_probability_le_on_good_event (w : WeightArray) (n : ℕ)
    (clocks : Fin (n + 1) → ℝ) (hinj : Function.Injective clocks)
    (k : Fin (n + 1)) {D d : ℝ} (hd : 0 < d) (hdD : d ≤ D)
    (hclose : |empiricalRemainingGe (w (n + 1)) clocks (orderTime clocks k) - D| ≤ d/2) :
    predictableChance (w (n + 1)) (raceDraw clocks) k ≤
      2 * (rowMaxRate w n / (n + 1 : ℕ)) / d := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hclose' : |(w (n + 1)).total (remaining (raceDraw clocks) k) /
      (n + 1 : ℕ) - D| ≤ d/2 := by
    rwa [remaining_weight_eq_empirical (w (n + 1)) clocks hinj k]
  calc
    predictableChance (w (n + 1)) (raceDraw clocks) k ≤
        (w (n + 1)).rate k / (w (n + 1)).total (remaining (raceDraw clocks) k) :=
      predictableChance_le_rate_div _ _ _
    _ = ((w (n + 1)).rate k / (n + 1 : ℕ)) /
        ((w (n + 1)).total (remaining (raceDraw clocks) k) / (n + 1 : ℕ)) :=
      (div_div_div_cancel_right₀ hn _ _).symm
    _ ≤ 2 * ((w (n + 1)).rate k / (n + 1 : ℕ)) / d :=
      probability_le_of_denominator_close (div_nonneg ((w (n + 1)).positive k).le
        (by positivity)) hd hdD hclose'
    _ ≤ 2 * (rowMaxRate w n / (n + 1 : ℕ)) / d := by
      gcongr
      exact rate_le_rowMaxRate w n k

/-- Equation `eq:interior-max-p`, for the actual remaining-set ratio.
The bound on the maximum rate and the denominator convergence are both
derived from the manuscript assumptions in the proof. -/
theorem section3_max_probability
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ predictableChance (w (n + 1)) (raceDraw clocks) k}) atTop (𝓝 0) := by
  intro ε hε
  by_cases hα0 : 0 ≤ α
  · let d : ℝ := profileD profileMeasure f (profileQuantile profileMeasure f α)
    have hd : 0 < d := (section3_denominator_lower hf hα0 hα).1
    have hsmall : Tendsto (fun n => 2 * (rowMaxRate w n / (n + 1 : ℕ)) / d)
        atTop (𝓝 0) := by
      simpa using (hf.max_weight_div_tendsto_zero.const_mul 2).div_const d
    have hevent : ∀ᶠ n in atTop, 2 * (rowMaxRate w n / (n + 1 : ℕ)) / d < ε :=
      hsmall.eventually (gt_mem_nhds hε)
    have hbound : ∀ᶠ n in atTop,
        exponentialRace (w (n + 1))
          {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
            ε ≤ predictableChance (w (n + 1)) (raceDraw clocks) k} ≤
        exponentialRace (w (n + 1))
          {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
            d/2 ≤ |empiricalRemainingGe (w (n + 1)) clocks (orderTime clocks k) -
              profileD profileMeasure f
                (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / (n + 1 : ℕ)))|} := by
      filter_upwards [hevent] with n hn
      apply measure_mono_ae
      filter_upwards [exponentialRace_injective_ae (w (n + 1))] with clocks hinj
      rintro ⟨k, hk, hp⟩
      refine ⟨k, hk, ?_⟩
      by_contra he
      have hclose := (lt_of_not_ge he).le
      have hlower := (section3_denominator_lower hf hα0 hα).2
        (((k.val : ℝ) + 1) / (n + 1 : ℕ)) ⟨by positivity, hk⟩
      have hupper := race_probability_le_on_good_event w n clocks hinj k hd hlower hclose
      exact (not_le_of_gt (hupper.trans_lt hn)) hp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (section3_uniform_denominator w f hnorm hf hα (d/2) (half_pos hd))
      (Eventually.of_forall fun _ => bot_le) hbound
  · have hempty (n : ℕ) :
        {clocks : Fin (n + 1) → ℝ | ∃ k : Fin (n + 1),
          ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
            ε ≤ predictableChance (w (n + 1)) (raceDraw clocks) k} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro clocks ⟨k, hk, _⟩
      exact hα0 ((by positivity : 0 ≤ ((k.val : ℝ) + 1) / (n + 1 : ℕ)).trans hk)
    simp_rw [hempty, measure_empty]
    exact tendsto_const_nhds

/-- The maximum conclusion of Proposition 3.2, with arbitrary row spaces
and the manuscript's original row index. -/
theorem section3_max_probability_general
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
        ε ≤ predictableChance (w n) (raceDraw (fun i => E n i ω)) k}) atTop (𝓝 0) := by
  intro ε hε
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (section3_max_probability w f hnorm hf hα ε hε) (fun _ => bot_le)
  intro n
  have hJoint : HasLaw (fun ω i => E (n + 1) i ω) (exponentialRace (w (n + 1)))
      (P (n + 1)) := (hIndependent (n + 1)).hasLaw_pi (hLaw (n + 1))
  dsimp only
  rw [← hJoint.map_eq]
  exact Measure.le_map_apply hJoint.aemeasurable _

end Luce
