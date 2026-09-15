import Luce.Section6EscapingCycleCylinder
import Luce.Section6RightEscapingPaths
import Luce.Section6LeftEscapingPaths
import Luce.Section6DominationMatrixRightTarget
import Luce.Section6DominationMatrixLeftTarget

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace Luce.Section6

/-- Actual right escaping-cycle probabilities. The decay exponent is
constructed from the profile, and no matrix or path estimate is an input. -/
theorem PowerProfile.right_excursion_cycle_probability {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (k : ℕ) :
    ∃ K kappa delta : ℝ, 0 < K ∧ 0 < kappa ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (v : Fin n) (B : ℝ), (terminalDepth v : ℝ) ≤ B →
      (terminalDepth v : ℝ)/(n : ℝ) ≤ delta →
      (exponentialRace (w n)).real {clocks |
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1 ∧
        ∃ z ∈ (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v).toFinset,
          B < (terminalDepth z : ℝ)} ≤
        K/(terminalDepth v : ℝ) * ((terminalDepth v : ℝ)^kappa/B^kappa) := by
  classical
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  let q := beta/2
  have hq : 0 < q := by dsimp [q]; positivity
  have hqb : q < beta := by dsimp [q]; linarith
  obtain ⟨C, hC, hpath⟩ := hp.right_escaping_path_bound hq hqb (k+1) (k+1) (by omega)
  obtain ⟨D, delta, hD, hd, hd1, htarget⟩ := hp.domination_matrix_right_target (k+1) (k+1) (by omega)
  refine ⟨D*((k : ℝ)+1)*C^k, q, delta, by positivity, hq, hd, hd1, ?_⟩
  intro grid w hw n v B hvB hv
  have hm : (0 : ℝ) < terminalDepth v := by exact_mod_cast terminalDepth_pos v
  have hB : 0 < B := hm.trans_le hvB
  let M := insertionDominationMatrix (w n) (k+1) (k+1)
  have hc := escaping_cycle_probability_le_paths (w n) (le_refl (k+1)) v
    (fun z => B < (terminalDepth z : ℝ)) (not_lt_of_ge hvB)
    (show 0 ≤ D/(terminalDepth v : ℝ) by positivity)
    (fun i => htarget grid w hw n i v hv)
  have hs : (∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        ∃ a, B < (terminalDepth (u a) : ℝ)), forwardPathWeight M v u) ≤
      (k : ℝ)*C^k*(terminalDepth v : ℝ)^q/B^q := by
    apply le_trans _ (hpath grid w hw n k v B hB)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hu).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha.le⟩
    · intro u hu hnot
      exact Finset.prod_nonneg (fun a _ => insertionDominationMatrix_nonneg (w n) (k+1) (k+1) _ _)
  apply hc.trans
  apply le_trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have hcoef : D/(terminalDepth v : ℝ)*((k : ℝ)*C^k) ≤
      D/(terminalDepth v : ℝ)*(((k : ℝ)+1)*C^k) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
  have hh := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ (terminalDepth v : ℝ)^q/B^q by positivity)
  convert hh using 1 <;> ring

/-- Actual left escaping-cycle probabilities, with the positive decay
exponent constructed internally from the manuscript's alpha>1. -/
theorem PowerProfile.left_excursion_cycle_probability {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (k : ℕ) :
    ∃ K kappa delta : ℝ, 0 < K ∧ 0 < kappa ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (v : Fin n) (A : ℝ), 0 < A → A ≤ (v.val : ℝ)+1 →
      ((v.val : ℝ)+1)/(n : ℝ) ≤ delta →
      (exponentialRace (w n)).real {clocks |
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1 ∧
        ∃ z ∈ (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v).toFinset,
          (z.val : ℝ)+1 < A} ≤
        K/((v.val : ℝ)+1) * ((1/((v.val : ℝ)+1)^kappa)/(1/A^kappa)) := by
  classical
  have halpha : 1 < alpha := hp.2.2.1.2.1
  let q := alpha/2
  have hq : 0 < q := by dsimp [q]; linarith
  have hqa : q < alpha := by dsimp [q]; linarith
  obtain ⟨C, hC, hpath⟩ := hp.left_escaping_path_bound hq hqa (k+1) (k+1) (by omega)
  obtain ⟨D, delta, hD, hd, hd1, htarget⟩ := hp.domination_matrix_left_target (k+1) (k+1) (by omega)
  refine ⟨D*((k : ℝ)+1)*C^k, q, delta, by positivity, hq, hd, hd1, ?_⟩
  intro grid w hw n v A hA hAv hv
  have hm : (0 : ℝ) < (v.val : ℝ)+1 := by positivity
  let M := insertionDominationMatrix (w n) (k+1) (k+1)
  have hc := escaping_cycle_probability_le_paths (w n) (le_refl (k+1)) v
    (fun z => (z.val : ℝ)+1 < A) (not_lt_of_ge hAv)
    (show 0 ≤ D/((v.val : ℝ)+1) by positivity)
    (fun i => htarget grid w hw n i v hv)
  have hs : (∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        ∃ a, ((u a).val : ℝ)+1 < A), forwardPathWeight M v u) ≤
      (k : ℝ)*C^k*(1/((v.val : ℝ)+1)^q)/(1/A^q) := by
    apply le_trans _ (hpath grid w hw n k v A hA)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hu).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha.le⟩
    · intro u hu hnot
      exact Finset.prod_nonneg (fun a _ => insertionDominationMatrix_nonneg (w n) (k+1) (k+1) _ _)
  apply hc.trans
  apply le_trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have hcoef : D/((v.val : ℝ)+1)*((k : ℝ)*C^k) ≤
      D/((v.val : ℝ)+1)*(((k : ℝ)+1)*C^k) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
  have hh := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ (1/((v.val : ℝ)+1)^q)/(1/A^q) by positivity)
  convert hh using 1 <;> ring

end Luce.Section6
