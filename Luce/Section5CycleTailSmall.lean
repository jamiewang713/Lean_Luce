import Luce.Section5TailExpectationBound

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce

/-- Full endpoint expectation control for each cycle length at least two.
The high-rate cutoff is chosen first, then the source/interior cutoff,
then delta, then the target cutoff, all before the eventual row. -/
theorem EndpointShellAssumption.cycle_tail_small_succ {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, α < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (∫ e, ((Section5.cycleCount (raceRankPermutation e) (k+1) -
        Section5.bulkCycleCount (raceRankPermutation e) α (k+1) : ℕ) : ℝ)
        ∂exponentialRace (w n)) < ε := by
  let l : ℝ := (k+2 : ℕ)
  have hl : 0 < l := by dsimp [l]; positivity
  have he : 0 < ε/(3*l) := by positivity
  obtain ⟨M, _, hM⟩ := hf.highCycleExpectation_small hnorm (k+2) he
  obtain ⟨J₀, _, hJ₀⟩ := hend.retained_expectation_tightness hnorm k
    (ε := ε/3) (by positivity)
  let β : ℝ := 1 - Real.exp (-(J₀ : ℝ))/2
  obtain ⟨δ, hδ, hlow⟩ := hf.interiorLowCycleExpectation_small hnorm (k+2) β
    (shellInteriorCutoff_lt_one J₀) he
  obtain ⟨J, _, hret⟩ := hJ₀ M δ hδ
  let α : ℝ := 1 - Real.exp (-(J : ℝ))/2
  refine ⟨α, shellInteriorCutoff_lt_one J, ?_⟩
  filter_upwards [hM M le_rfl, hlow δ hδ le_rfl, hret,
    eventually_exterior_shellNumber J] with n hnM hnLow hnRet hnDeep
  have hbound := tail_cycle_expectation_le_retained_and_truncations
    w n (k+1) J M β δ α hnDeep
  have hscale : l * (ε/(3*l)) = ε/3 := by field_simp
  have hhigh : l * highCycleExpectation w (k+2) n M < ε/3 := by
    simpa only [hscale] using mul_lt_mul_of_pos_left hnM hl
  have hsmall : l * interiorLowCycleExpectation w (k+2) n β δ < ε/3 := by
    simpa only [hscale] using mul_lt_mul_of_pos_left hnLow hl
  change _ ≤ _ + l * _ at hbound
  rw [mul_add] at hbound
  linarith

end Luce
