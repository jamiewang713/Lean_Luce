import Luce.Section6CriticalDeletionFloor
import Luce.Section5GapReservoir

noncomputable section
open MeasureTheory
namespace Luce.Section6

theorem CriticalProfile.deleted_remaining_floor {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card),
      1 ≤ q.val → removed.card ≤ q.val → 4*q.val ≤ n →
      Z ≤ Real.log ((n : ℝ)/q.val) →
      ∀ σ, (c/2)*(n : ℝ)*Real.log ((n : ℝ)/q.val) ≤
        orderedRemainingRate (compactDeletedWeights (w n) removed) σ q := by
  obtain ⟨C,hC,hfloor⟩ := hp.remaining_weight_floor
  have hc : 0 < c := hp.2.2.1
  refine ⟨max 2 (2*Real.log 4+2*C/c),le_max_left _ _,?_⟩
  intro grid w hw n removed q hq hr hqn hz σ
  have hqp : (0 : ℝ) < q.val := by exact_mod_cast (show 0 < q.val by omega)
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh := hfloor grid w hw n (4*q.val) (by omega) hqn
    (deletedPrefixLabels removed σ q) ((deletedPrefixLabels_card_le removed σ q).trans (by omega))
  rw [total_compl_deletedPrefixLabels] at hh
  have he : Real.log ((n : ℝ)/(4*q.val : ℕ)) = Real.log ((n : ℝ)/q.val)-Real.log 4 := by
    push_cast
    rw [Real.log_div hnp.ne' (by positivity),Real.log_mul (by norm_num) hqp.ne',
      Real.log_div hnp.ne' hqp.ne']
    ring
  rw [he] at hh
  have hzC := (le_max_right _ _).trans hz
  have hmul := mul_le_mul_of_nonneg_left hzC hc.le
  have heq : c*(2*Real.log 4+2*C/c) = 2*c*Real.log 4+2*C := by field_simp
  rw [heq] at hmul
  have hnn := mul_le_mul_of_nonneg_left hmul hnp.le
  nlinarith

end Luce.Section6
