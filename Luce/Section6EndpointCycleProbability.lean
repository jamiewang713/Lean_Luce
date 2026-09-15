import Luce.Section6CycleVertexBound
import Luce.Section6DominationMatrixRightTarget
import Luce.Section6DominationMatrixLeftTarget

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace Luce.Section6

/-- Actual cycle-through-vertex probability at an active right endpoint.
Every matrix premise is discharged from original profile/sampling inputs. -/
theorem PowerProfile.right_cycle_vertex_probability {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (k : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ v : Fin n, (terminalDepth v : ℝ)/(n : ℝ) ≤ delta →
      (exponentialRace (w n)).real {clocks |
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1} ≤
        C/(terminalDepth v : ℝ) := by
  obtain ⟨B, hB, hrow⟩ := hp.domination_matrix_row_bound_all_n (k+1) (k+1) (by omega)
  obtain ⟨D, delta, hD, hd, hd1, htarget⟩ := hp.domination_matrix_right_target (k+1) (k+1) (by omega)
  refine ⟨D*B^k, delta, mul_pos hD (pow_pos hB k), hd, hd1, ?_⟩
  intro grid w hw n v hv
  have ht := cycle_vertex_probability_le_matrix_rows (w n) (le_refl (k+1)) v hB.le
    (show 0 ≤ D/(terminalDepth v : ℝ) by positivity)
    (fun i => hrow grid w hw n i Finset.univ)
    (fun i => htarget grid w hw n i v hv)
  simpa only [div_mul_eq_mul_div] using ht

/-- Actual cycle-through-vertex probability at an active left endpoint. -/
theorem PowerProfile.left_cycle_vertex_probability {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (k : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ v : Fin n, ((v.val : ℝ)+1)/(n : ℝ) ≤ delta →
      (exponentialRace (w n)).real {clocks |
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1} ≤ C/((v.val : ℝ)+1) := by
  obtain ⟨B, hB, hrow⟩ := hp.domination_matrix_row_bound_all_n (k+1) (k+1) (by omega)
  obtain ⟨D, delta, hD, hd, hd1, htarget⟩ := hp.domination_matrix_left_target (k+1) (k+1) (by omega)
  refine ⟨D*B^k, delta, mul_pos hD (pow_pos hB k), hd, hd1, ?_⟩
  intro grid w hw n v hv
  have ht := cycle_vertex_probability_le_matrix_rows (w n) (le_refl (k+1)) v hB.le
    (show 0 ≤ D/((v.val : ℝ)+1) by positivity)
    (fun i => hrow grid w hw n i Finset.univ)
    (fun i => htarget grid w hw n i v hv)
  simpa only [div_mul_eq_mul_div] using ht

end Luce.Section6
