import Luce.Section6Proposition65Sum
import Luce.Section6Lemma64Matrix

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace Luce.Section6

/-- The full quantitative local law, including its interval consequence,
with the exact independently frozen assumptions and kernels. -/
theorem proposition65_localLaw : Proposition65Contract.localLaw := by
  classical
  intro f left right hp grid w hw r
  obtain ⟨h0, delta, d, kappa, C, hh0, hd, hd1, hdecay, hk, hk8, hC, hsum⟩ :=
    hp.proposition65_sum grid w hw r
  let R : ℝ := max 1 (r : ℝ)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  have hCC : C ≤ C*R := by nlinarith only [hC, hR1]
  refine ⟨h0, delta, 1/16, d, kappa, C*R, hh0, hd, hd1,
    by norm_num, by norm_num, hdecay, hk, mul_pos hC hR0, ?_⟩
  intro n s hsr side u j hu hj hactive hlarge hsmall hmoderate hsep
  let err := |(exponentialRace (w n)).real {clocks | MarkedRankCylinder u j clocks} -
    ∏ e, localIdealKernel (side e) (cornerBehavior left right (side e))
      (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e))|
  let envelope := ∏ e, localEnvelopeKernel (side e) (cornerBehavior left right (side e)) d
    (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e))
  let E : Fin s → ℝ := fun e => localPowerError kappa n
    (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e))
  have henv : 0 ≤ envelope := Finset.prod_nonneg (fun e _ =>
    (localEnvelopeKernel_positive _ _ _ (cornerDistance_positive _ _) (cornerDistance_positive _ _)).le)
  have hE : ∀ e, 0 ≤ E e := fun e => localPowerError_nonneg
    (Nat.cast_pos.mpr (Nat.zero_lt_of_lt (j e).isLt))
    (Nat.cast_pos.mpr (cornerDistance_positive _ _)) (Nat.cast_pos.mpr (cornerDistance_positive _ _))
  have hEsum : 0 ≤ ∑ e, E e := Finset.sum_nonneg (fun e _ => hE e)
  have hbound : err ≤ C*envelope*(∑ e, E e) := by
    by_cases hs : s = 0
    · subst s
      simp [err, envelope, MarkedRankCylinder]
    · exact hsum n s (Nat.pos_of_ne_zero hs) hsr side u j hu hj hactive hlarge hsmall hmoderate hsep
  dsimp only
  change err ≤ (C*R)*envelope*(∑ e, E e) ∧
    ∀ A B : ℝ, 0 < A →
      (∀ e, A ≤ (cornerDistance (side e) (u e) : ℝ) ∧
        A ≤ (cornerDistance (side e) (j e) : ℝ) ∧
        (cornerDistance (side e) (u e) : ℝ) ≤ B ∧
        (cornerDistance (side e) (j e) : ℝ) ≤ B) →
      err ≤ (C*R)*(A^(-kappa)+(B/(n : ℝ))^kappa)*envelope
  constructor
  · exact hbound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC henv) hEsum)
  · intro A B hA hab
    let T := A^(-kappa)+(B/(n : ℝ))^kappa
    have hT : 0 ≤ T := add_nonneg (Real.rpow_nonneg hA.le _)
      (small_rpow_nonneg hk.le (by linarith only [hk8]) _)
    have hsumbound : (∑ e, E e) ≤ R*T := by
      calc
        _ ≤ ∑ _e : Fin s, T := Finset.sum_le_sum (fun e _ => localPowerError_interval hk
          (Nat.cast_pos.mpr (Nat.zero_lt_of_lt (j e).isLt)) hA
          (hab e).1 (hab e).2.1 (hab e).2.2.1 (hab e).2.2.2)
        _ = (s : ℝ)*T := by simp
        _ ≤ R*T := mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr hsr).trans (le_max_right _ _)) hT
    calc
      err ≤ C*envelope*(∑ e, E e) := hbound
      _ ≤ C*envelope*(R*T) := mul_le_mul_of_nonneg_left hsumbound (mul_nonneg hC.le henv)
      _ = _ := by dsimp [T]; ring

/-- Proposition 6.5 in full: the local estimate and its interval form,
and the global matrix conclusion for every other configuration. -/
theorem proposition65 : Proposition65Contract.proposition65 :=
  ⟨proposition65_localLaw, lemma64_matrix⟩

end Luce.Section6
