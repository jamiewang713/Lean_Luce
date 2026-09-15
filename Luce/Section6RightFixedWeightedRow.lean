import Luce.Section6KernelLpOne
import Luce.Section6SampledWeightedSubsets

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- A fixed number of terminal targets has bounded right weighted row mass.
Uses the proved norm bound by one, valid even for the infinite final gap. -/
theorem right_fixed_targets_weighted_row {kappa : ℝ} (hk : 0 ≤ kappa) (H : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (w : Weights n) (i : Fin n)
      (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n)) (q : Fin n → ℕ) (p : ℝ≥0∞),
    (∀ j ∈ s, terminalDepth j ≤ H) →
    (∑ j ∈ s, ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel w (removed j) old i (q j)).toReal)
        p (exponentialRace w)) ≤ ENNReal.ofReal C := by
  let K : ℝ := ((H : ℝ)+1)^kappa
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨((H : ℝ)+1)*K, by positivity, ?_⟩
  intro n w i s removed q p hs
  have ha : (1 : ℝ) ≤ terminalDepth i := by exact_mod_cast terminalDepth_pos i
  have hterm : ∀ j ∈ s,
      ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel w (removed j) old i (q j)).toReal)
        p (exponentialRace w) ≤ ENNReal.ofReal K := by
    intro j hj
    have hh : (terminalDepth j : ℝ) ≤ H := by exact_mod_cast hs j hj
    have hratio : (terminalDepth j : ℝ)/(terminalDepth i : ℝ) ≤ (H : ℝ)+1 :=
      (div_le_self (Nat.cast_nonneg _) ha).trans (by linarith)
    have hw := Real.rpow_le_rpow (by positivity) hratio hk
    have he := mul_le_mul (ENNReal.ofReal_le_ofReal hw)
      (deleted_kernel_eLpNorm_le_one w (removed j) i (q j) p) zero_le zero_le
    simpa only [mul_one] using he
  classical
  have hinj : Set.InjOn (terminalDepth : Fin n → ℕ) s := by
    intro a ha b hb hab
    apply Fin.ext
    unfold terminalDepth at hab
    have ha' := a.isLt
    have hb' := b.isLt
    omega
  have hsub : s.image terminalDepth ⊆ Finset.Ico 1 (H+1) := by
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_Ico.mpr ⟨terminalDepth_pos j, Nat.lt_succ_of_le (hs j hj)⟩
  have hcard : s.card ≤ H := by
    have he := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hinj] at he
    simpa using he
  calc
    _ ≤ ∑ _j ∈ s, ENNReal.ofReal K := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((s.card : ℝ)*K) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hK.le)]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh : (s.card : ℝ) ≤ H := by exact_mod_cast hcard
      exact mul_le_mul_of_nonneg_right (by linarith : (s.card : ℝ) ≤ (H : ℝ)+1) hK.le

end Luce.Section6
