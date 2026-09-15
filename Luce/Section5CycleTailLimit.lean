import Luce.Section5CycleTailSmall

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce

def cycleTailExpectation (w : WeightArray) (k n : ℕ) (α : ℝ) : ℝ :=
  ∫ e, ((Section5.cycleCount (raceRankPermutation e) k -
    Section5.bulkCycleCount (raceRankPermutation e) α k : ℕ) : ℝ) ∂exponentialRace (w n)

theorem cycleTailExpectation_nonneg (w : WeightArray) (k n : ℕ) (α : ℝ) :
    0 ≤ cycleTailExpectation w k n α := integral_nonneg (fun _ => Nat.cast_nonneg _)

theorem cycleTailExpectation_antitone (w : WeightArray) (k n : ℕ) :
    Antitone (cycleTailExpectation w k n) := by
  intro α β hαβ
  apply integral_mono (integrable_race_permutation_statistic (w n)
    (fun R => ((Section5.cycleCount R k - Section5.bulkCycleCount R β k : ℕ) : ℝ)))
    (integrable_race_permutation_statistic (w n)
      (fun R => ((Section5.cycleCount R k - Section5.bulkCycleCount R α k : ℕ) : ℝ)))
  intro e
  apply Nat.cast_le.mpr
  rw [Section5.tailCycleCount_eq_maximum_roots, Section5.tailCycleCount_eq_maximum_roots]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hroot, hvβ⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hroot,
    (mul_le_mul_of_nonneg_right hαβ (Nat.cast_nonneg n)).trans_lt hvβ⟩

/-- A real limsup is used only after proving the relevant row sequence
eventually bounded above and nonnegative. -/
theorem cycleTailExpectation_limit_of_small (w : WeightArray) (k : ℕ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, α < 1 ∧
      ∀ᶠ n in atTop, cycleTailExpectation w k n α < ε) :
    Tendsto (fun α : ℝ => limsup (fun n => cycleTailExpectation w k n α) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨α₀, hα₀, hrows⟩ := hsmall (ε/2) (by positivity)
  have hnear : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), α₀ < α :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hα₀)
  filter_upwards [hnear] with α hα
  have hevent : ∀ᶠ n in atTop, cycleTailExpectation w k n α ≤ ε/2 :=
    hrows.mono fun n hn => (cycleTailExpectation_antitone w k n hα.le).trans hn.le
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => cycleTailExpectation w k n α) :=
    ⟨ε/2, hevent⟩
  have hlo : 0 ≤ limsup (fun n => cycleTailExpectation w k n α) atTop :=
    le_limsup_of_frequently_le (Eventually.of_forall
      (fun n => cycleTailExpectation_nonneg w k n α)).frequently hb
  have hup : limsup (fun n => cycleTailExpectation w k n α) atTop ≤ ε/2 :=
    limsup_le_of_le (isCoboundedUnder_le_of_le atTop
      (fun n => cycleTailExpectation_nonneg w k n α)) hevent
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

theorem EndpointShellAssumption.cycle_tail_limit_succ {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (k : ℕ) :
    Tendsto (fun α : ℝ => limsup (fun n => cycleTailExpectation w (k+1) n α) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
  cycleTailExpectation_limit_of_small w (k+1)
    (fun ε hε => hend.cycle_tail_small_succ hnorm hf k hε)

end Luce
