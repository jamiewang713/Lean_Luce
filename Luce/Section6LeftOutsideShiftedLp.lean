import Luce.Section6ShiftedKernelComparison
import Luce.Section6GapOffsets

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The outside-left ordinary insertion kernel in the manuscript's demanded
rank h, uniformly over bounded deletions and shifts of the actual gap. -/
theorem PowerProfile.left_outside_shifted_insertion_Lp {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (p0 : ℕ) :
    ∃ C d delta : ℝ, 0 < C ∧ 0 < d ∧ 0 < delta ∧ delta ≤ sigma ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 0 < n → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) ≤ delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    Nat.dist q.val (h-1) ≤ r+1 → sigma ≤ ((i.val : ℝ)+1)/(n : ℝ) →
    1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*((w n).rate i*((h : ℝ)/(n : ℝ))^alpha/(h : ℝ))*
        Real.exp (-d*((w n).rate i*((h : ℝ)/(n : ℝ))^alpha))) := by
  obtain ⟨B, delta, hB, hd, hds, hb⟩ := hp.left_outside_insertion_Lp hsigma hsigma1 p0
  have ha : 0 ≤ alpha := (lt_trans zero_lt_one hp.2.2.1.2.1).le
  have hpow : 0 < (2 : ℝ)^alpha := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨B*(2*(2 : ℝ)^alpha), 1/(2 : ℝ)^alpha, delta/2,
    by positivity, by positivity, half_pos hd, (by linarith), ?_⟩
  intro grid w hw n r h hn hh hsmall removed hremoved i q p hshift hi hpp hpp0
  obtain ⟨hq, hqh, hhq⟩ := shifted_left_gap_bounds hh hshift
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hqR : (0 : ℝ) < q.val := Nat.cast_pos.mpr (by omega)
  have hqhR : (q.val : ℝ) ≤ 2*(h : ℝ) := by exact_mod_cast hqh
  have hhqR : (h : ℝ) ≤ 2*(q.val : ℝ) := by exact_mod_cast hhq
  have hqn : (q.val : ℝ)/(n : ℝ) ≤ delta := by
    have hh' := (div_le_iff₀ hnR).mp hsmall
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  apply (hb grid w hw n r hn removed hremoved i q p hq hqn hi hpp hpp0).trans
  apply ENNReal.ofReal_le_ofReal
  have hir := (w n).positive i
  have hx := mul_le_mul_of_nonneg_left
    (scaled_power_le_of_depth_le hqR.le hhR.le hnR ha hqhR) hir.le
  have hy := mul_le_mul_of_nonneg_left
    (scaled_power_le_of_depth_le hhR.le hqR.le hnR ha hhqR) hir.le
  have hx' : (w n).rate i*((q.val : ℝ)/(n : ℝ))^alpha ≤
      (2 : ℝ)^alpha*((w n).rate i*((h : ℝ)/(n : ℝ))^alpha) := by nlinarith [hx]
  have hy' : (w n).rate i*((h : ℝ)/(n : ℝ))^alpha ≤
      (2 : ℝ)^alpha*((w n).rate i*((q.val : ℝ)/(n : ℝ))^alpha) := by nlinarith [hy]
  have he := shifted_exponential_kernel_bound (by positivity) (by positivity)
    hqR hhR hpow hhqR hx' hy'
  have hm := mul_le_mul_of_nonneg_left he hB.le
  simpa only [mul_assoc] using hm

end Luce.Section6
