import Luce.Section6LeftArrivalDeletion
import Luce.Section6LeftWeightedDeletion
import Luce.Section6RightSurvivorDeletion
import Luce.Section6RightWeightedDeletion

noncomputable section
namespace Luce.Section6

/-- Both fast-endpoint population formulas, with one positive error
exponent and one constant, uniform over all sets of at most r deletions. -/
theorem PowerProfile.left_deleted_populations_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) (r : ℕ) :
    ∃ zeta K : ℝ, 0 < zeta ∧ 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ (removed : Finset (Fin n)), removed.card ≤ r →
    ∀ t : ℝ, 0 < t → t ≤ 1 →
    (|deletedG (w n) removed t /
        (Real.Gamma (1-1/alpha)*c^(1/alpha)*t^(1/alpha)) - 1| ≤
      K*(t^zeta+1/((n : ℝ)*t^(1/alpha)))) ∧
    (|deletedD (w n) removed 1 t /
        ((Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha-1)) - 1| ≤
      K*(t^zeta+1/((n : ℝ)*t^(1/alpha)))) := by
  obtain ⟨zG, KG, hzG, hKG, hG⟩ := h.left_deletedG_relative_error r
  obtain ⟨zD, KD, hzD, hKD, hD⟩ := h.left_deletedD_relative_error r
  refine ⟨min zG zD, KG+KD, lt_min hzG hzD, add_pos hKG hKD, ?_⟩
  intro grid w hw n hn removed hr t ht ht1
  have hE : 0 ≤ t^(min zG zD)+1/((n : ℝ)*t^(1/alpha)) := by positivity
  have hg := Real.rpow_le_rpow_of_exponent_ge ht ht1 (min_le_left zG zD)
  have hd := Real.rpow_le_rpow_of_exponent_ge ht ht1 (min_le_right zG zD)
  constructor
  · exact (hG grid w hw n hn removed hr t ht ht1).trans
      ((mul_le_mul_of_nonneg_left (add_le_add hg (le_refl _)) hKG.le).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hKD.le) hE))
  · exact (hD grid w hw n hn removed hr t ht ht1).trans
      ((mul_le_mul_of_nonneg_left (add_le_add hd (le_refl _)) hKD.le).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hKG.le) hE))

/-- Both slow-endpoint population formulas with the exact Gamma constants
and the same eta/beta error exponent, including bounded deletions. -/
theorem PowerProfile.right_deleted_populations_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ (removed : Finset (Fin n)), removed.card ≤ r →
    ∀ t : ℝ, 1 ≤ t →
    (|deletedH (w n) removed t /
        (Real.Gamma (1+1/beta)*c^(-(1/beta))*t^(-(1/beta))) - 1| ≤
      K*(t^(-(eta/beta))+1/((n : ℝ)*t^(-(1/beta))))) ∧
    (|deletedD (w n) removed 1 t /
        ((Real.Gamma (1+1/beta)*c^(-(1/beta))/beta)*t^(-1-1/beta)) - 1| ≤
      K*(t^(-(eta/beta))+1/((n : ℝ)*t^(-(1/beta))))) := by
  obtain ⟨KH, hKH, hH⟩ := h.right_deletedH_relative_error r
  obtain ⟨KD, hKD, hD⟩ := h.right_deletedD_relative_error r
  refine ⟨KH+KD, add_pos hKH hKD, ?_⟩
  intro grid w hw n hn removed hr t ht1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hE : 0 ≤ t^(-(eta/beta))+1/((n : ℝ)*t^(-(1/beta))) := by positivity
  exact ⟨(hH grid w hw n hn removed hr t ht1).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hKD.le) hE),
    (hD grid w hw n hn removed hr t ht1).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hKH.le) hE)⟩

end Luce.Section6
