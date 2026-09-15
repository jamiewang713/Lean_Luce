import Luce.Section6Lemma64Matrix
import Luce.Section6FactorialKernelRows

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

/-- The matrix data used in the factorial comparison are conclusions of
Lemma 6.4 on the sampled race. No matrix bound is a model assumption. -/
theorem PowerProfile.factorial_domination_data {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray)
    (hw : SampledRates grid w f) (r : ℕ) :
    ∃ (M : (n : ℕ) → Fin n → Fin n → ℝ) (C delta kappa : ℝ),
      1 ≤ C ∧ 0 < delta ∧ 0 < kappa ∧
      (∀ n (a b : Fin n), 0 ≤ M n a b) ∧
      (∀ n t, t ≤ r → ∀ u j : Fin t → Fin n, Function.Injective u → Function.Injective j →
        (exponentialRace (w n)).real {e | MarkedRankCylinder u j e} ≤ C*∏ a, M n (u a) (j a)) ∧
      (∀ n a, (∑ b, M n a b) ≤ C) ∧
      (∀ side, (cornerBehavior left right side).active →
        (∀ n (b : Fin n), (cornerDistance side b : ℝ) ≤ delta*(n : ℝ) →
          ∀ a, M n a b ≤ C/(cornerDistance side b : ℝ)) ∧
        (∀ n (a : Fin n), (∑ b, (cornerRowRatio side (cornerDistance side a)
          (cornerDistance side b))^kappa*M n a b) ≤ C)) := by
  obtain ⟨M, C, delta, kappa, v, d, nu, H, hC, hd, hd1, hk, hv, hv1,
    hparams, hM, hcyl, hrow, hinterior, hleft, hright⟩ := lemma64_matrix f left right hp grid w hw r
  refine ⟨M, max 1 C, delta, kappa, le_max_left _ _, hd, hk, hM, ?_, ?_, ?_⟩
  · intro n t htr u j hu hj
    exact (hcyl n t htr u j hu hj).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.prod_nonneg (fun a _ => hM n _ _)))
  · intro n a
    exact (hrow n a).trans (le_max_right _ _)
  · intro side hactive
    have hbound :
        (∀ n (b : Fin n), (cornerDistance side b : ℝ)/(n : ℝ) ≤ delta →
          ∀ a, M n a b ≤ C/(cornerDistance side b : ℝ)) ∧
        (∀ n (a : Fin n), (∑ b, (cornerRowRatio side (cornerDistance side a)
          (cornerDistance side b))^kappa*M n a b) ≤ C) := by
      cases side with
      | left =>
        cases left with
        | finite c => exact False.elim hactive
        | power c alpha eta =>
          have h := hleft c alpha eta rfl
          constructor
          · intro n b hb
            have hb' : ((b.val : ℝ)+1)/(n : ℝ) ≤ delta := by
              simpa [cornerDistance, Nat.cast_add, Nat.cast_one] using hb
            simpa [cornerDistance, Nat.cast_add, Nat.cast_one] using (h.1 n b hb').1
          · simpa [cornerRowRatio, cornerDistance, Nat.cast_add, Nat.cast_one] using h.2.1
      | right =>
        cases right with
        | finite c => exact False.elim hactive
        | power c beta eta =>
          have h := hright c beta eta rfl
          exact ⟨fun n b hb => (h.1 n b hb).1, h.2.1⟩
    constructor
    · intro n b hb a
      have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt b.isLt)
      exact (hbound.1 n b ((div_le_iff₀ hn).mpr hb) a).trans
        (div_le_div_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _))
    · intro n a
      exact (hbound.2 n a).trans (le_max_right _ _)

end Luce.Section6
