import Luce.Section6LeftTailMean
import Luce.Section6GapStartTail
import Luce.Section6GapOffsets

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- The manuscript left endpoint order-statistic lower tail, for the actual
deleted gap start and bounded demanded-rank shifts. No mean bound is assumed. -/
theorem PowerProfile.left_gap_start_lower_tail {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ k H rho : ℝ, 0 < k ∧ k ≤ 1 ∧ 0 < H ∧ 0 < rho ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 0 < n → h ≤ n → H ≤ (h : ℝ) → 8*r+8 ≤ h →
    ∀ (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card),
    Nat.dist q.val (h-1) ≤ r+1 →
    (exponentialRace (w n)).real {old |
      raceGapStart (compactDeletedClocks removed old) q < k*((h : ℝ)/(n : ℝ))^alpha} ≤
      Real.exp (-rho*(h : ℝ)) := by
  obtain ⟨k, H, hk, hk1, hH, hmean⟩ := hp.left_early_deleted_mean
  have hc := log_two_sub_half_pos
  refine ⟨k, H, (Real.log 2-1/2)/2, hk, hk1, hH, div_pos hc (by norm_num), ?_⟩
  intro grid w hw n r h hn hhn hhH hh removed q hshift
  have hhpos : 0 < h := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ht : 0 < k*((h : ℝ)/(n : ℝ))^alpha :=
    mul_pos hk (Real.rpow_pos_of_pos (div_pos (Nat.cast_pos.mpr hhpos) hnR) _)
  have hq := (shifted_left_gap_bounds hh hshift).2.2
  have hqR : (h : ℝ) ≤ 2*(q.val : ℝ) := by exact_mod_cast hq
  have hm : (n : ℝ)*deletedG (w n) removed (k*((h : ℝ)/(n : ℝ))^alpha) ≤ (q.val : ℝ)/2 :=
    (hmean grid w hw n h hn hhpos hhn hhH removed).trans (by linarith)
  apply (deleted_gap_start_tail_of_arrival_mean (w n) hn removed q ht.le hm).trans
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hqR hc.le]

end Luce.Section6
