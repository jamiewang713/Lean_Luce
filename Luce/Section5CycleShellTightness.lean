import Luce.Section5SingletonTail

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce

def shortCycleTailExpectation (w : WeightArray) (L n : ℕ) (α : ℝ) : ℝ :=
  ∑ k : Fin L, cycleTailExpectation w k.val n α

theorem shortCycleTailExpectation_eq_integral (w : WeightArray) (L n : ℕ) (α : ℝ) :
    shortCycleTailExpectation w L n α =
      ∫ e, (∑ k : Fin L, (Section5.cycleCount (raceRankPermutation e) k.val -
        Section5.bulkCycleCount (raceRankPermutation e) α k.val : ℕ) : ℝ)
        ∂exponentialRace (w n) := by
  exact (integral_finsetSum _ (fun k _ => integrable_race_permutation_statistic (w n)
    (fun R => ((Section5.cycleCount R k.val - Section5.bulkCycleCount R α k.val : ℕ) : ℝ)))).symm

theorem shortCycleTailExpectation_nonneg (w : WeightArray) (L n : ℕ) (α : ℝ) :
    0 ≤ shortCycleTailExpectation w L n α :=
  Finset.sum_nonneg fun k _ => cycleTailExpectation_nonneg w k.val n α

theorem shortCycleTailExpectation_antitone (w : WeightArray) (L n : ℕ) :
    Antitone (shortCycleTailExpectation w L n) := by
  intro α β hαβ
  exact Finset.sum_le_sum fun k _ => cycleTailExpectation_antitone w k.val n hαβ

theorem EndpointShellAssumption.short_cycle_tail_small {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, α < 1 ∧ ∀ᶠ n : ℕ in atTop, shortCycleTailExpectation w L n α < ε := by
  classical
  by_cases hL : L = 0
  · subst L
    exact ⟨0, by norm_num, Eventually.of_forall (fun n => by simpa [shortCycleTailExpectation] using hε)⟩
  haveI : Nonempty (Fin L) := ⟨⟨0, Nat.pos_of_ne_zero hL⟩⟩
  have hd : 0 < ε/((L : ℝ)+1) := by positivity
  choose a ha hrows using fun k : Fin L => hend.cycle_tail_small hnorm hf k.val hd
  let A : ℝ := Finset.univ.sup' Finset.univ_nonempty a
  have hA : A < 1 := (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun k _ => ha k)
  have haA (k : Fin L) : a k ≤ A := Finset.le_sup' a (Finset.mem_univ k)
  refine ⟨A, hA, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hrows] with n hn
  calc
    _ ≤ ∑ _k : Fin L, ε/((L : ℝ)+1) := Finset.sum_le_sum (fun k _ =>
      (cycleTailExpectation_antitone w k.val n (haA k)).trans (hn k).le)
    _ = (L : ℝ) * (ε/((L : ℝ)+1)) := by simp
    _ < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by positivity : 0 < (L : ℝ)+1)).mpr
      nlinarith

/-- The revised manuscript's complete short-cycle endpoint expectation
limit. Its only model hypotheses are normalization, profile convergence,
and the exact raw endpoint shell condition. -/
theorem EndpointShellAssumption.cycle_shell_tightness {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) :
    Tendsto (fun α : ℝ => limsup (fun n : ℕ =>
      ∫ e, (∑ k : Fin L, (Section5.cycleCount (raceRankPermutation e) k.val -
        Section5.bulkCycleCount (raceRankPermutation e) α k.val : ℕ) : ℝ)
        ∂exponentialRace (w n)) atTop) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  simp_rw [← shortCycleTailExpectation_eq_integral]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨α₀, hα₀, hrows⟩ := hend.short_cycle_tail_small hnorm hf L
    (ε := ε/2) (by positivity)
  have hnear : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), α₀ < α :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hα₀)
  filter_upwards [hnear] with α hα
  have hevent : ∀ᶠ n in atTop, shortCycleTailExpectation w L n α ≤ ε/2 :=
    hrows.mono fun n hn => (shortCycleTailExpectation_antitone w L n hα.le).trans hn.le
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => shortCycleTailExpectation w L n α) :=
    ⟨ε/2, hevent⟩
  have hlo : 0 ≤ limsup (fun n => shortCycleTailExpectation w L n α) atTop :=
    le_limsup_of_frequently_le (Eventually.of_forall
      (fun n => shortCycleTailExpectation_nonneg w L n α)).frequently hb
  have hup : limsup (fun n => shortCycleTailExpectation w L n α) atTop ≤ ε/2 :=
    limsup_le_of_le (isCoboundedUnder_le_of_le atTop
      (fun n => shortCycleTailExpectation_nonneg w L n α)) hevent
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

end Luce
