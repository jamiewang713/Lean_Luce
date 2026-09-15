import Luce.Section5ExceptionalLow

/-! Revised truncation order: low-rate labels on a fixed interior interval.
There is no endpoint assumption, and no restriction delta < gamma. -/
noncomputable section
open MeasureTheory Filter Set Function
open scoped BigOperators Topology
namespace Luce
attribute [local instance] Classical.propDecidable

def interiorLowCycleExpectation (w : WeightArray) (L n : ℕ) (α δ : ℝ) : ℝ :=
  ∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L
    (Finset.univ.filter (fun v => (w n).rate v < δ ∧
      (v.val : ℝ)+1 ≤ α*n)) : ℝ) ∂exponentialRace (w n)

theorem interiorLowCycleExpectation_nonneg (w : WeightArray) (L n : ℕ) (α δ : ℝ) :
    0 ≤ interiorLowCycleExpectation w L n α δ :=
  integral_nonneg (fun _ => Nat.cast_nonneg _)

theorem ProfileLimit.interiorLowCycleExpectation_bound {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (L : ℕ) (α : ℝ) (hα : α < 1) (M : ℝ) (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, ∀ᶠ n : ℕ in atTop,
      interiorLowCycleExpectation w L n α δ ≤
        (L : ℝ)*highCycleExpectation w L n M + K*lowRateDensity w n δ := by
  obtain ⟨C, hC, hprob⟩ := hf.bounded_cycle_probability_uniform L M hM hα
  refine ⟨(L : ℝ)*C+1, by positivity, ?_⟩
  intro δ
  filter_upwards [hprob] with n hn
  let S := Finset.univ.filter (fun v : Fin n => (w n).rate v < δ ∧ (v.val : ℝ)+1 ≤ α*n)
  let H := Finset.univ.filter (fun v : Fin n => M < (w n).rate v)
  have hbulk (v : Fin n) (hv : v ∈ S) : (v.val : ℝ)+1 ≤ α*n :=
    (Finset.mem_filter.mp hv).2.2
  have hcard : (S.card : ℝ) ≤ (Finset.univ.filter (fun v : Fin n => (w n).rate v < δ)).card := by
    exact_mod_cast Finset.card_le_card (show S ⊆ Finset.univ.filter (fun v : Fin n => (w n).rate v < δ) from by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.1⟩)
  have hAvoid : (∫ clocks, (shortCycleVertexCountAvoiding (raceRankPermutation clocks)
      L S H : ℝ) ∂exponentialRace (w n)) ≤ ((L : ℝ)*C+1)*lowRateDensity w n δ := by
    calc
      _ ≤ ∑ v ∈ S, ∑ k : Fin L,
          (exponentialRace (w n)).real (boundedCycleEvent (w n) k.val M v) :=
        shortCycleVertexCountAvoiding_expectation_le (w n) L M S
      _ ≤ ∑ _v ∈ S, ∑ _k : Fin L, C/n :=
        Finset.sum_le_sum (fun v hv => Finset.sum_le_sum (fun k _ => hn v (hbulk v hv) k))
      _ = ((L : ℝ)*C)*(S.card/n) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ ((L : ℝ)*C)*lowRateDensity w n δ :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg n)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact (shortCycleVertexCount_expectation_le_high_add_avoiding (w n) L S H).trans
    (add_le_add le_rfl hAvoid)

theorem ProfileLimit.interiorLowCycleExpectation_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) (L : ℕ)
    (α : ℝ) (hα : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n : ℕ in atTop, interiorLowCycleExpectation w L n α δ < ε := by
  obtain ⟨M, hM, hhigh⟩ := hf.highCycleExpectation_small hnorm L
    (ε := ε/(2*((L : ℝ)+1))) (by positivity)
  obtain ⟨K, hK, hlow⟩ := hf.interiorLowCycleExpectation_bound L α hα M hM
  obtain ⟨d, hd, hsmall⟩ := hf.lowRateDensity_small (ε := ε/(2*K)) (by positivity)
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδd
  filter_upwards [hlow δ, hhigh M le_rfl, hsmall δ hδ hδd] with n hb hh hl
  have hL : 0 < (L : ℝ)+1 := by positivity
  have hh' : (L : ℝ)*highCycleExpectation w L n M < ε/2 := by
    calc
      _ ≤ ((L : ℝ)+1)*highCycleExpectation w L n M :=
        mul_le_mul_of_nonneg_right (by linarith) (highCycleExpectation_nonneg w L n M)
      _ < ((L : ℝ)+1)*(ε/(2*((L : ℝ)+1))) := mul_lt_mul_of_pos_left hh hL
      _ = ε/2 := by field_simp
  have hl' : K*lowRateDensity w n δ < ε/2 := by
    calc
      _ < K*(ε/(2*K)) := mul_lt_mul_of_pos_left hl hK
      _ = ε/2 := by field_simp
  linarith

theorem ProfileLimit.interior_low_rate_cycles_vanish {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) (L : ℕ)
    (α : ℝ) (hα : α < 1) :
    Tendsto (fun δ : ℝ => limsup (fun n => interiorLowCycleExpectation w L n α δ) atTop)
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ₀, hδ₀, hsmall⟩ := hf.interiorLowCycleExpectation_small hnorm L α hα
    (ε := ε/2) (by positivity)
  have hnear : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < δ₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hδ₀)
  filter_upwards [self_mem_nhdsWithin, hnear] with δ hδ hδ₀'
  have hseq := hsmall δ hδ hδ₀'.le
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => interiorLowCycleExpectation w L n α δ) :=
    ⟨ε/2, hseq.mono (fun _ h => h.le)⟩
  have hlo : 0 ≤ limsup (fun n => interiorLowCycleExpectation w L n α δ) atTop :=
    le_limsup_of_frequently_le (Eventually.of_forall
      (fun n => interiorLowCycleExpectation_nonneg w L n α δ)).frequently hb
  have hup : limsup (fun n => interiorLowCycleExpectation w L n α δ) atTop ≤ ε/2 :=
    limsup_le_of_le (isCoboundedUnder_le_of_le atTop
      (fun n => interiorLowCycleExpectation_nonneg w L n α δ)) (hseq.mono (fun _ h => h.le))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

end Luce
