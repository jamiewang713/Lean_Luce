import Luce.Section6RightSurvivorDeletion
import Luce.Section6JointErrorCutoffs
import Luce.Section6QuantileComparability

noncomputable section
namespace Luce.Section6

/-- A uniform lower survivor envelope after bounded deletion. The region
and all error cutoffs are derived from the original profile. -/
theorem PowerProfile.right_deletedH_lower_region {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ S M : ℝ, 1 ≤ S ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ t : ℝ, S ≤ t → M ≤ (n : ℝ)*t^(-(1/beta)) →
      (Real.Gamma (1+1/beta)*c^(-(1/beta))*t^(-(1/beta)))/2 ≤ deletedH (w n) removed t := by
  have hc := hp.2.2.2.1.1
  have hb := hp.2.2.2.1.2.1
  have he := hp.2.2.2.1.2.2.1
  obtain ⟨K, hK, herr⟩ := hp.right_deletedH_relative_error r
  obtain ⟨d, M, hd, hM, hsmall⟩ := joint_power_error_small (div_pos he hb) hK
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨max 1 (2/d), M, le_max_left _ _, hM, ?_⟩
  intro grid w hw n hn removed hremoved t ht hm
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have htd : 1/t < d := by
    apply (div_lt_iff₀ ht0).mpr
    have hh := (div_le_iff₀ hd).mp ((le_max_right _ _).trans ht)
    nlinarith
  have hh := hsmall (1/t) ((n : ℝ)*t^(-(1/beta))) (one_div_pos.mpr ht0) htd hm
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow] at hh
  have hbound := (herr grid w hw n hn removed hremoved t ht1).trans hh
  apply (half_relative_error_bounds _ hbound).1
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  positivity

end Luce.Section6
