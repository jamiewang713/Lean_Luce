import Luce.Section7RankIntegral
import Luce.Section7TailIntegral

/-! # Proposition 7.1: the independent-clock terminal fixed-point bound -/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace Luce.Section7
noncomputable section

theorem clockRace_tail_integrals {n : ℕ} (g : Fin n → ClockDensity)
    (candidate : ℕ → Fin n) {M : ℕ} {B s : ℝ} (h : ℝ → ℝ)
    (hM : 1 ≤ M) (hBM : 2 * (M : ℝ) ≤ B - 1) (hcut : survivorMean g s = B)
    (hh : IntegrableOn h (Ioi s))
    (henv : ∀ m ∈ Finset.Icc 1 M, ∀ t ≥ s, (g (candidate m)).density t ≤ h t) :
    (∑ m ∈ Finset.Icc 1 M, ∫ t, (g (candidate m)).density t *
      survivorProbability g (candidate m) (m - 1) t) ≤
      (M : ℝ) * Real.exp (-tailConstant * B) + 2 * ∫ t in Ioi s, h t := by
  have hbound := density_integral_bound (Finset.Icc 1 M)
    (fun m => g (candidate m)) (fun m => survivorProbability g (candidate m) (m - 1))
    s (Real.exp (-tailConstant * B)) h (Real.exp_pos _).le hh
    (fun m _ => measurable_survivorProbability g (candidate m) (m - 1))
    (fun _ _ _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
    (fun m hm t ht => survivorProbability_early g (candidate m)
      (Finset.mem_Icc.mp hm).2 hM ht hcut hBM)
    (fun t ht => ((g (candidate 1)).nonneg t).trans
      (henv 1 (Finset.mem_Icc.mpr ⟨le_rfl, hM⟩) t ht.le))
    (fun m hm t ht => henv m hm t ht.le)
    (fun t _ => sum_survivorProbability_le_two g candidate M t)
  simpa using hbound

/-- Proposition `prop:general-clock-tail`, for the product clock law.
The universal constant is explicitly `(1/2 - exp(-1))/2`. -/
theorem clockRace_tail {n M : ℕ} (g : Fin n → ClockDensity)
    (hM : 1 ≤ M) (hMn : M ≤ n) {B s : ℝ} (h : ℝ → ℝ)
    (hBM : 2 * (M : ℝ) ≤ B - 1) (hcut : survivorMean g s = B)
    (hh : IntegrableOn h (Ioi s))
    (henv : ∀ m ∈ Finset.Icc 1 M, ∀ t ≥ s,
      (g (terminalLabel n (by omega) m)).density t ≤ h t) :
    (∑ m ∈ Finset.Icc 1 M, (clockRace g).real
      {e | rankOf e (terminalLabel n (by omega) m) = n - m + 1}) ≤
      (M : ℝ) * Real.exp (-tailConstant * B) + 2 * ∫ t in Ioi s, h t := by
  have heq : (∑ m ∈ Finset.Icc 1 M, (clockRace g).real
      {e | rankOf e (terminalLabel n (by omega) m) = n - m + 1}) =
      ∑ m ∈ Finset.Icc 1 M, ∫ t, (g (terminalLabel n (by omega) m)).density t *
        survivorProbability g (terminalLabel n (by omega) m) (m - 1) t := by
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    rw [clockRace_rank_integral g _ _ (by omega) (by omega),
      show n - (n - m + 1) = m - 1 by omega]
  rw [heq]
  exact clockRace_tail_integrals g _ h hM hBM hcut hh henv

/-- **Section 7 main theorem.** Independent clocks on an arbitrary probability
space, with only the density, cutoff, and envelope hypotheses in the paper.
Integrability of the envelope is needed only on the late-time half-line. -/
theorem general_clock_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n M : ℕ} (g : Fin n → ClockDensity)
    (T : Fin n → Ω → ℝ) (hLaw : ∀ i, HasLaw (T i) (g i).law P)
    (hIndependent : iIndepFun T P) (hM : 1 ≤ M) (hMn : M ≤ n)
    {B s : ℝ} (h : ℝ → ℝ) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hcut : (∑ i, P.real {ω | s < T i ω}) = B)
    (hh : IntegrableOn h (Ioi s))
    (henv : ∀ m ∈ Finset.Icc 1 M, ∀ t ≥ s,
      (g (terminalLabel n (by omega) m)).density t ≤ h t) :
    (∑ m ∈ Finset.Icc 1 M, P.real
      {ω | rankOf (fun i => T i ω) (terminalLabel n (by omega) m) = n - m + 1}) ≤
      (M : ℝ) * Real.exp (-tailConstant * B) + 2 * ∫ t in Ioi s, h t := by
  have hj : HasLaw (fun ω i => T i ω) (clockRace g) P :=
    hIndependent.hasLaw_pi hLaw
  have hc : survivorMean g s = B := by
    rw [← hcut]
    apply Finset.sum_congr rfl
    intro i _
    exact ((hLaw i).measureReal_eq measurableSet_Ioi).symm
  have heq : (∑ m ∈ Finset.Icc 1 M, P.real
      {ω | rankOf (fun i => T i ω) (terminalLabel n (by omega) m) = n - m + 1}) =
      ∑ m ∈ Finset.Icc 1 M, (clockRace g).real
      {e | rankOf e (terminalLabel n (by omega) m) = n - m + 1} := by
    apply Finset.sum_congr rfl
    intro m _
    exact hj.measureReal_eq ((measurable_rankOf _) (measurableSet_singleton _))
  rw [heq]
  exact clockRace_tail g hM hMn h hBM hc hh henv

end
end Luce.Section7
