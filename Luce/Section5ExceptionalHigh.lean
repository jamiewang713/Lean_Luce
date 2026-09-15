import Luce.Section5HighRates
import Luce.Section5CycleProbability
import Luce.Section5Predecessor
import Luce.Section5VertexCount

/-!
# The high-rate half of Proposition 5.4

Source: `fixed_points.tex:1187–1206`. Combine the literal ghost-cylinder
comparison, density domination, and the added-predecessor lemma. Every
expectation is integrable under the actual exponential race law.
-/

noncomputable section
open MeasureTheory Filter Set Function
open scoped BigOperators Topology

namespace Luce
attribute [local instance] Classical.propDecidable

/-- The single-vertex estimate used in the high-rate proof. The finite
half-mass hypothesis is the one proved eventually from the original assumptions. -/
theorem high_rate_cycle_vertex_probability {n : ℕ} (w : Weights n) (k : ℕ) (M : ℝ)
    (hmass : (n : ℝ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => w.rate i ≤ M), w.rate i)
    (v : Fin n) (hv : M < w.rate v) :
    (exponentialRace w).real {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1} ≤
      (2 * w.rate v / n) * (predecessorConstant (k + 1) k : ℝ) := by
  let B := fun old : Fin n → ℝ =>
    ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        Function.Injective u ∧ ∀ a, u a ≠ v),
      ghostColumn w (k + 1) old ((Fin.snoc u v : Fin (k + 1) → Fin n) 0) *
        ∏ a : Fin k, ghostEntry w (k + 1) old (u a)
          ((Fin.snoc u v : Fin (k + 1) → Fin n) a.succ)
  have hB : Integrable B (exponentialRace w) := added_predecessor_integrable w (k + 1) v
  have hscale : 0 ≤ 2 * w.rate v / (n : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) (w.positive v).le) (Nat.cast_nonneg _)
  calc
    _ ≤ ∫ old, ghostCycleVertexSum w k v old ∂exponentialRace w :=
      cycle_vertex_probability_le_ghost w k v
    _ ≤ ∫ old, (2 * w.rate v / n) * B old ∂exponentialRace w := by
      apply integral_mono_ae (ghostCycleVertexSum_integrable w k v) (hB.const_mul _)
      filter_upwards [exponentialRace_nonnegative_background w] with old hold
      dsimp only [ghostCycleVertexSum, B]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u _
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right
        (high_rate_ghostEntry_bound w (k + 1) M hmass old hold v _ hv)
      exact Finset.prod_nonneg (fun a _ => (ghostEntry_mem_Icc w (k + 1) old _ _).1)
    _ = (2 * w.rate v / n) * ∫ old, B old ∂exponentialRace w := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (added_predecessor w (k + 1) v) hscale

/-- A uniform constant for the sum over all lengths from 1 through L. -/
def highCycleConstant (L : ℕ) : ℕ :=
  2 * ∑ k : Fin L, predecessorConstant (k.val + 1) k.val

/-- Quantitative high-rate vertex bound in (1204–1206). The left side counts
vertices in H, not all vertices of cycles which happen to meet H. -/
theorem high_rate_cycle_vertices_bound {n : ℕ} (w : Weights n) (L : ℕ) (M : ℝ)
    (hmass : (n : ℝ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => w.rate i ≤ M), w.rate i) :
    (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L
      (Finset.univ.filter (fun v => M < w.rate v)) : ℝ) ∂exponentialRace w) ≤
      (highCycleConstant L : ℝ) *
        ((∑ v ∈ Finset.univ.filter (fun v => M < w.rate v), w.rate v) / n) := by
  calc
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v => M < w.rate v), ∑ k : Fin L,
        (exponentialRace w).real {clocks |
          minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k.val + 1} :=
      shortCycleVertexCount_expectation_le w L _
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v => M < w.rate v), ∑ k : Fin L,
        (2 * w.rate v / n) * (predecessorConstant (k.val + 1) k.val : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact Finset.sum_le_sum (fun k _ =>
        high_rate_cycle_vertex_probability w k.val M hmass v (Finset.mem_filter.mp hv).2)
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div,
        highCycleConstant, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
      ring

/-- The actual expectation in the high-rate part of Proposition 5.4. -/
def highCycleExpectation (w : WeightArray) (L n : ℕ) (M : ℝ) : ℝ :=
  ∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L
    (Finset.univ.filter (fun v => M < (w n).rate v)) : ℝ) ∂exponentialRace (w n)

lemma highCycleExpectation_nonneg (w : WeightArray) (L n : ℕ) (M : ℝ) :
    0 ≤ highCycleExpectation w L n M := integral_nonneg (fun _ => Nat.cast_nonneg _)

/-- High-rate cycles vanish under exactly the source's normalization and
profile assumptions. Endpoint control is unnecessary for this half. -/
theorem ProfileLimit.highCycleExpectation_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) (L : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∀ᶠ n : ℕ in atTop, highCycleExpectation w L n M < ε := by
  have hC : 0 ≤ (highCycleConstant L : ℝ) := Nat.cast_nonneg _
  have hCp : 0 < (highCycleConstant L : ℝ) + 1 := by positivity
  obtain ⟨A, hA, hmass⟩ := hf.eventually_moderate_half_mass hnorm
  obtain ⟨B, hB, hsmall⟩ := hf.highRateMass_small
    (ε := ε / ((highCycleConstant L : ℝ) + 1)) (div_pos hε hCp)
  refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
  intro M hM
  filter_upwards [hmass M ((le_max_left _ _).trans hM),
    hsmall M ((le_max_right _ _).trans hM)] with n hn hs
  have hnneg : 0 ≤ highRateMass w n M := by
    unfold highRateMass
    exact div_nonneg (Finset.sum_nonneg (fun v _ => (w n).positive v |>.le))
      (Nat.cast_nonneg _)
  calc
    highCycleExpectation w L n M ≤ (highCycleConstant L : ℝ) * highRateMass w n M :=
      high_rate_cycle_vertices_bound (w n) L M hn
    _ ≤ ((highCycleConstant L : ℝ) + 1) * highRateMass w n M :=
      mul_le_mul_of_nonneg_right (by linarith) hnneg
    _ < ((highCycleConstant L : ℝ) + 1) * (ε / ((highCycleConstant L : ℝ) + 1)) :=
      mul_lt_mul_of_pos_left hs hCp
    _ = ε := mul_div_cancel₀ ε hCp.ne'

/-- Literal iterated-limit statement in the high-rate half of Proposition
5.4. Eventual upper boundedness is proved before using the real limsup, so
the totalized limsup operation cannot mask an unbounded sequence. -/
theorem ProfileLimit.high_rate_cycles_vanish {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) (L : ℕ) :
    Tendsto (fun M : ℝ => limsup (fun n => highCycleExpectation w L n M) atTop)
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M₀, _, hM⟩ := hf.highCycleExpectation_small hnorm L
    (ε := ε / 2) (by positivity)
  refine ⟨M₀, fun M hMM => ?_⟩
  have hseq := hM M hMM
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => highCycleExpectation w L n M) :=
    ⟨ε / 2, hseq.mono (fun _ hn => hn.le)⟩
  have hlo : 0 ≤ limsup (fun n => highCycleExpectation w L n M) atTop :=
    le_limsup_of_frequently_le
      (Eventually.of_forall (fun n => highCycleExpectation_nonneg w L n M)).frequently hb
  have hup : limsup (fun n => highCycleExpectation w L n M) atTop ≤ ε / 2 :=
    limsup_le_of_le (isCoboundedUnder_le_of_le atTop
      (fun n => highCycleExpectation_nonneg w L n M)) (hseq.mono (fun _ hn => hn.le))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

end Luce
