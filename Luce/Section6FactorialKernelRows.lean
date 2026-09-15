import Luce.Section6LeftOrdinaryWeightedRow
import Luce.Section6LocalCornerData
import Luce.Section6LocalCoefficientComparison
import Luce.Section6SampledWeightedSubsets
import Luce.Section6LogExcursionAlgebra

noncomputable section
open scoped BigOperators
namespace Luce.Section6

def cornerRowRatio (side : Corner) (a b : ℕ) : ℝ :=
  match side with
  | .left => (a : ℝ)/(b : ℝ)
  | .right => (b : ℝ)/(a : ℝ)

def cornerDepthPotential (side : Corner) (kappa : ℝ) (a : ℕ) : ℝ :=
  match side with
  | .left => (a : ℝ)^(-kappa)
  | .right => (a : ℝ)^kappa

theorem local_envelope_weighted_rows (side : Corner) (behavior : EndpointBehavior)
    {d kappa : ℝ} (hd : 0 < d) (hg : 0 < localCornerExponent behavior)
    (hk : kappa < localCornerExponent behavior) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (a : Fin n),
      (∑ b : Fin n, (cornerRowRatio side (cornerDistance side a) (cornerDistance side b))^kappa *
        localEnvelopeKernel side behavior d (cornerDistance side a) (cornerDistance side b)) ≤ C := by
  have hs : ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ, 0 < a → ∀ n : ℕ,
      (∑ b ∈ Finset.Ico 1 (n+1), (cornerRowRatio side a b)^kappa *
        localEnvelopeKernel side behavior d a b) ≤ C := by
    cases side with
    | left =>
      obtain ⟨C, hC, hc⟩ := left_ordinary_weighted_row_bound hg hk hd
      refine ⟨C, hC, fun a ha n => ?_⟩
      simpa [cornerRowRatio, localEnvelopeKernel, localCornerRatio, mul_assoc] using
        hc (a : ℝ) (Nat.cast_pos.mpr ha) n
    | right =>
      obtain ⟨C, hC, hc⟩ := right_ordinary_weighted_row_bound hg hk hd
      refine ⟨C, hC, fun a ha n => ?_⟩
      simpa [cornerRowRatio, localEnvelopeKernel, localCornerRatio, mul_assoc] using
        hc (a : ℝ) (Nat.cast_pos.mpr ha) n
  obtain ⟨C, hC, hc⟩ := hs
  refine ⟨C, hC, fun n a => ?_⟩
  have he := positive_depth_subset_sum_le (Finset.univ : Finset (Fin n))
    (cornerDistance side) (cornerDistance_injective67 side)
    (fun b => ⟨cornerDistance_positive side b, by cases side <;> dsimp [cornerDistance] <;> omega⟩)
    (fun b => (cornerRowRatio side (cornerDistance side a) b)^kappa *
      localEnvelopeKernel side behavior d (cornerDistance side a) b)
    (fun b hb => mul_nonneg (by cases side <;> simp only [cornerRowRatio] <;> positivity)
      (localEnvelopeKernel_positive side behavior d (cornerDistance_positive side a) hb).le)
  exact he.trans (hc (cornerDistance side a) (cornerDistance_positive side a) n)

theorem local_envelope_target_bound (side : Corner) (behavior : EndpointBehavior)
    {d : ℝ} (hd : 0 < d) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    localEnvelopeKernel side behavior d a b ≤ (1/d)/(b : ℝ) := by
  have hx := (localCornerRatio_positive side behavior ha hb).le
  have ht := div_le_div_of_nonneg_right (linear_exponential_bound hd hx) (Nat.cast_nonneg b)
  simpa [localEnvelopeKernel, div_mul_eq_mul_div] using ht

/-- Uniform ordinary, weighted, and target bounds for the actual slack
envelope, derived from its fixed formula. -/
theorem local_envelope_matrix_bounds (side : Corner) (behavior : EndpointBehavior)
    {d kappa : ℝ} (hd : 0 < d) (hg : 0 < localCornerExponent behavior)
    (hk : kappa < localCornerExponent behavior) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ n (a b : Fin n), 0 ≤ localEnvelopeKernel side behavior d
        (cornerDistance side a) (cornerDistance side b)) ∧
      (∀ n (a : Fin n), (∑ b : Fin n, localEnvelopeKernel side behavior d
        (cornerDistance side a) (cornerDistance side b)) ≤ C) ∧
      (∀ n (a b : Fin n), localEnvelopeKernel side behavior d
        (cornerDistance side a) (cornerDistance side b) ≤ C/(cornerDistance side b : ℝ)) ∧
      (∀ n (a : Fin n), (∑ b : Fin n, (cornerRowRatio side (cornerDistance side a) (cornerDistance side b))^kappa *
        localEnvelopeKernel side behavior d (cornerDistance side a) (cornerDistance side b)) ≤ C) := by
  obtain ⟨C0, h0, hr⟩ := local_envelope_weighted_rows side behavior hd hg (kappa := 0) hg
  obtain ⟨Cw, hw, hwr⟩ := local_envelope_weighted_rows side behavior hd hg hk
  have hdi : 0 < 1/d := one_div_pos.mpr hd
  refine ⟨1+C0+Cw+1/d, by linarith, ?_, ?_, ?_, ?_⟩
  · intro n a b
    exact (localEnvelopeKernel_positive side behavior d (cornerDistance_positive side a)
      (cornerDistance_positive side b)).le
  · intro n a
    have hh := hr n a
    simp only [Real.rpow_zero, one_mul] at hh
    exact hh.trans (by linarith)
  · intro n a b
    exact (local_envelope_target_bound side behavior hd (cornerDistance_positive side a)
      (cornerDistance_positive side b)).trans
        (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  · intro n a
    exact (hwr n a).trans (by linarith)

theorem local_ideal_eq_scaled_envelope (side : Corner) (behavior : EndpointBehavior) (a b : ℕ) :
    localIdealKernel side behavior a b =
      (localCornerExponent behavior*localCornerQ side behavior)*
        localEnvelopeKernel side behavior (localCornerQ side behavior) a b := by
  unfold localIdealKernel localEnvelopeKernel
  ring

end Luce.Section6
