import Luce.Section6OneGapMoment
import Luce.Section5GapLaw

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- The starting time reconstructed from normalized spacings strictly before q. -/
def gapStartFromNormalized {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n))
    (q : Fin n) (ξ : Fin n → ℝ) : ℝ :=
  ∑ l ∈ Finset.Iio q, ξ l / orderedRemainingRate w σ l

/-- Telescoping includes the initial gap with its zero sentinel. -/
theorem sum_previous_gaps {n : ℕ} (c : Fin n → ℝ) (q : Fin n) :
    ((Finset.Iio q).sum (fun l : Fin n => c l - previousOrderedTime c l)) =
      previousOrderedTime c q := by
  cases n with
  | zero => exact Fin.elim0 q
  | succ n =>
    induction q using Fin.induction with
    | zero =>
      have hz : Finset.Iio (0 : Fin (n+1)) = ∅ := by
        ext l
        simp
      rw [hz, Finset.sum_empty]
      simp [previousOrderedTime]
    | succ i ih =>
      have hi : Finset.Iio i.succ = insert i.castSucc (Finset.Iio i.castSucc) := by
        ext l
        simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff,
          Fin.val_succ, Fin.val_castSucc]
        omega
      rw [hi, Finset.sum_insert (by simp), ih]
      simp [previousOrderedTime]
      rfl

theorem gapStartFromNormalized_eq_previous {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) (c : Fin n → ℝ) :
    gapStartFromNormalized w σ q (orderedNormalizedGaps w σ c) =
      previousOrderedTime (fun l => c (σ l)) q := by
  unfold gapStartFromNormalized
  simp_rw [← ordered_gap_eq_normalized_div_rate]
  exact sum_previous_gaps _ q

/-- The start depends only on earlier spacings, never on the current spacing. -/
theorem gapStartFromNormalized_congr {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) {ξ ζ : Fin n → ℝ}
    (h : ∀ l < q, ξ l = ζ l) :
    gapStartFromNormalized w σ q ξ = gapStartFromNormalized w σ q ζ := by
  apply Finset.sum_congr rfl
  intro l hl
  rw [h l (Finset.mem_Iio.mp hl)]

theorem continuous_gapStartFromNormalized {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) :
    Continuous (gapStartFromNormalized w σ q) := by
  unfold gapStartFromNormalized
  fun_prop

theorem gapStartFromNormalized_nonneg {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) {ξ : Fin n → ℝ}
    (hξ : ∀ l < q, 0 ≤ ξ l) : 0 ≤ gapStartFromNormalized w σ q ξ := by
  apply Finset.sum_nonneg
  intro l hl
  exact div_nonneg (hξ l (Finset.mem_Iio.mp hl)) (orderedRemainingRate_pos w σ l).le

/-- Updating the current spacing leaves the starting time unchanged. -/
theorem gapStartFromNormalized_update {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) (ξ : Fin n → ℝ) (z : ℝ) :
    gapStartFromNormalized w σ q (Function.update ξ q z) =
      gapStartFromNormalized w σ q ξ := by
  apply gapStartFromNormalized_congr
  intro l hl
  exact Function.update_of_ne (ne_of_lt hl) z ξ

/-- Integrate the current spacing while retaining every preceding coordinate.
This is the literal coordinate slice, before applying the joint product law. -/
theorem gap_moment_coordinate_slice {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) (ξ : Fin n → ℝ)
    {a : ℝ} (ha : 0 < a) (p : ℕ) :
    Integrable (fun z => exponentialGapMass a
      (gapStartFromNormalized w σ q (Function.update ξ q z))
      ((Function.update ξ q z) q / orderedRemainingRate w σ q)^p) (expMeasure 1) ∧
    (∫ z, exponentialGapMass a
      (gapStartFromNormalized w σ q (Function.update ξ q z))
      ((Function.update ξ q z) q / orderedRemainingRate w σ q)^p ∂expMeasure 1) ≤
      (p.factorial : ℝ)*(a/orderedRemainingRate w σ q)^p*
        Real.exp (-((p : ℝ)*a*gapStartFromNormalized w σ q ξ)) := by
  simp only [gapStartFromNormalized_update, Function.update_self]
  exact one_gap_moment_bound ha (orderedRemainingRate_pos w σ q) _ p

end Luce.Section6
