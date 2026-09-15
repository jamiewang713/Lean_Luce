import Luce.Section5LowCycleProbability
import Luce.Section5ExceptionalHigh
import Luce.Section5LowRates

/-!
# Proposition 5.4: exceptional vertices in short cycles

Source: `fixed_points.tex:1162–1240`. The low-rate bound is assembled
from actual restricted cycle probabilities and the orbit counting
inequality. The final theorem includes both iterated limits.
-/

noncomputable section
open MeasureTheory Filter Set Function
open scoped BigOperators Topology
namespace Luce
attribute [local instance] Classical.propDecidable

/-- The literal low-rate expectation of the manuscript's V_(n,L). -/
def lowCycleExpectation (w : WeightArray) (L n : ℕ) (δ : ℝ) : ℝ :=
  ∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L
    (Finset.univ.filter (fun v => (w n).rate v < δ)) : ℝ) ∂exponentialRace (w n)

lemma lowCycleExpectation_nonneg (w : WeightArray) (L n : ℕ) (δ : ℝ) :
    0 ≤ lowCycleExpectation w L n δ := integral_nonneg (fun _ => Nat.cast_nonneg _)

/-- Quantitative inequality at source 1233–1237. The endpoint hypothesis
places all low labels strictly in the interior. There is no assumption
ε₀<1: if that interval is empty, the label condition proves it empty. -/
theorem ProfileLimit.lowCycleExpectation_bound {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) (L : ℕ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ M : ℝ, 0 < M → ∃ K : ℝ, 0 < K ∧
      ∀ δ : ℝ, 0 < δ → δ < γ → ∀ᶠ n : ℕ in atTop,
        lowCycleExpectation w L n δ ≤
          (L : ℝ) * highCycleExpectation w L n M + K * lowRateDensity w n δ := by
  obtain ⟨γ, ε₀, n₀, hγ, hε₀, he⟩ := hend
  refine ⟨γ, hγ, ?_⟩
  intro M hM
  let α : ℝ := 1 - ε₀ / 2
  have hα : α < 1 := by dsimp [α]; linarith
  obtain ⟨C, hC, hprob⟩ := hf.bounded_cycle_probability_uniform L M hM hα
  refine ⟨(L : ℝ) * C + 1, by positivity, ?_⟩
  intro δ _hδ hδγ
  filter_upwards [hprob, eventually_ge_atTop n₀] with n hn hn₀
  let S := Finset.univ.filter (fun v : Fin n => (w n).rate v < δ)
  let H := Finset.univ.filter (fun v : Fin n => M < (w n).rate v)
  have hbulk (v : Fin n) (hv : v ∈ S) : (v.val : ℝ) + 1 ≤ α * n := by
    have hlow : (w n).rate v < γ := ((Finset.mem_filter.mp hv).2).trans hδγ
    have hidx : (v.val : ℝ) + 1 < (1 - ε₀) * n := by
      by_contra! h
      exact (not_le_of_gt hlow) (he n hn₀ v h)
    have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [α]
    nlinarith
  have hAvoid : (∫ clocks, (shortCycleVertexCountAvoiding (raceRankPermutation clocks)
        L S H : ℝ) ∂exponentialRace (w n)) ≤
      ((L : ℝ) * C + 1) * lowRateDensity w n δ := by
    calc
      _ ≤ ∑ v ∈ S, ∑ k : Fin L,
          (exponentialRace (w n)).real (boundedCycleEvent (w n) k.val M v) :=
        shortCycleVertexCountAvoiding_expectation_le (w n) L M S
      _ ≤ ∑ _v ∈ S, ∑ _k : Fin L, C / n :=
        Finset.sum_le_sum (fun v hv => Finset.sum_le_sum (fun k _ => hn v (hbulk v hv) k))
      _ = ((L : ℝ) * C) * lowRateDensity w n δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          lowRateDensity, S]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact (shortCycleVertexCount_expectation_le_high_add_avoiding (w n) L S H).trans
    (add_le_add le_rfl hAvoid)

/-- Quantified version of the low-rate limit, with the row threshold
chosen after δ, as required by the iterated limit in the manuscript. -/
theorem ProfileLimit.lowCycleExpectation_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w)
    (hend : EndpointAssumption w) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n : ℕ in atTop, lowCycleExpectation w L n δ < ε := by
  obtain ⟨γ, hγ, hbound⟩ := hf.lowCycleExpectation_bound hend L
  obtain ⟨M, hM, hhigh⟩ := hf.highCycleExpectation_small hnorm L
    (ε := ε / (2 * ((L : ℝ) + 1))) (by positivity)
  obtain ⟨K, hK, hlow⟩ := hbound M hM
  obtain ⟨d, hd, hsmall⟩ := hf.lowRateDensity_small (ε := ε / (2 * K)) (by positivity)
  refine ⟨min d (γ / 2), lt_min hd (by positivity), ?_⟩
  intro δ hδ hδ₀
  have hδd := hδ₀.trans (min_le_left _ _)
  have hδγ : δ < γ := (hδ₀.trans (min_le_right _ _)).trans_lt (by linarith)
  filter_upwards [hlow δ hδ hδγ, hhigh M le_rfl, hsmall δ hδ hδd] with n hb hh hl
  have hL : 0 < (L : ℝ) + 1 := by positivity
  have hh' : (L : ℝ) * highCycleExpectation w L n M < ε / 2 := by
    calc
      _ ≤ ((L : ℝ) + 1) * highCycleExpectation w L n M :=
        mul_le_mul_of_nonneg_right (by linarith) (highCycleExpectation_nonneg w L n M)
      _ < ((L : ℝ) + 1) * (ε / (2 * ((L : ℝ) + 1))) := mul_lt_mul_of_pos_left hh hL
      _ = ε / 2 := by field_simp
  have hl' : K * lowRateDensity w n δ < ε / 2 := by
    calc
      _ < K * (ε / (2 * K)) := mul_lt_mul_of_pos_left hl hK
      _ = ε / 2 := by field_simp
  linarith

/-- The literal low-rate iterated limit in Proposition 5.4. Eventual
boundedness and nonnegativity are established before invoking real limsup. -/
theorem ProfileLimit.low_rate_cycles_vanish {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w)
    (hend : EndpointAssumption w) (L : ℕ) :
    Tendsto (fun δ : ℝ => limsup (fun n => lowCycleExpectation w L n δ) atTop)
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ₀, hδ₀, hsmall⟩ := hf.lowCycleExpectation_small hnorm hend L
    (ε := ε / 2) (by positivity)
  have hnear : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < δ₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hδ₀)
  filter_upwards [self_mem_nhdsWithin, hnear] with δ hδ hδ₀'
  have hseq := hsmall δ hδ hδ₀'.le
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => lowCycleExpectation w L n δ) :=
    ⟨ε / 2, hseq.mono (fun _ h => h.le)⟩
  have hlo : 0 ≤ limsup (fun n => lowCycleExpectation w L n δ) atTop :=
    le_limsup_of_frequently_le
      (Eventually.of_forall (fun n => lowCycleExpectation_nonneg w L n δ)).frequently hb
  have hup : limsup (fun n => lowCycleExpectation w L n δ) atTop ≤ ε / 2 :=
    limsup_le_of_le (isCoboundedUnder_le_of_le atTop
      (fun n => lowCycleExpectation_nonneg w L n δ)) (hseq.mono (fun _ h => h.le))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

/-- The whole of Proposition 5.4, under exactly the standing normalization
and the two numbered assumptions. The two counts retain strict rate cutoffs. -/
theorem section5_proposition54 (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (hend : EndpointAssumption w) (L : ℕ) :
    Tendsto (fun M : ℝ => limsup (fun n => highCycleExpectation w L n M) atTop)
      atTop (𝓝 0) ∧
    Tendsto (fun δ : ℝ => limsup (fun n => lowCycleExpectation w L n δ) atTop)
      (𝓝[>] 0) (𝓝 0) :=
  ⟨hf.high_rate_cycles_vanish hnorm L, hf.low_rate_cycles_vanish hnorm hend L⟩

end Luce
