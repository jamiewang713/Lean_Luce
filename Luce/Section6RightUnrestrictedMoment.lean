import Luce.Section6RightInsertionMoment
import Luce.Section6DepthComparison

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Right insertion moments with the original source rate, uniformly over
bounded deletions and demanded-rank shifts. No source-block restriction. -/
theorem PowerProfile.right_unrestricted_shifted_moment {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ B : ℝ, 0 < B ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 0 < n → h ≤ n → 8*r+8 ≤ h →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    Nat.dist q.val (n-h) ≤ r+1 →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*(B*((w n).rate i*((n : ℝ)/(h : ℝ))^beta/(h : ℝ)))^p*
      (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*
        raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace (w n)) := by
  obtain ⟨C, hC, hm⟩ := hp.right_deleted_insertion_moment
  refine ⟨(1/C)*(2 : ℝ)^(beta+1), by positivity, ?_⟩
  intro grid w hw n r h hn hhn hh removed hremoved i q p hshift
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hir := (w n).positive i
  obtain ⟨hq, hhm, _⟩ := shifted_right_survivor_bounds hremoved hhn hh hshift
  let m := n-removed.card-q.val
  have hm0 : 0 < m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hcount : m+removed.card+q.val ≤ n := by dsimp [m]; omega
  have hhmR : (h : ℝ) ≤ 2*(m : ℝ) := by exact_mod_cast hhm
  have hratio : (w n).rate i/(C*(n : ℝ)^(-beta)*(m : ℝ)^(beta+1)) =
      (1/C)*((w n).rate i*((n : ℝ)/(m : ℝ))^beta/(m : ℝ)) := by
    have he := right_insertion_ratio_identity (K := (w n).rate i) (a := (n : ℝ))
      (beta := beta) hC hnR hnR hmR
    simpa [hnR.ne', div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using he
  have hc := right_depth_factor_comparison hnR hmR hhR hp.2.2.2.1.2.1.le hhmR
  have hb := mul_le_mul_of_nonneg_left hc (show 0 ≤ (1/C)*(w n).rate i by positivity)
  have hb' : (w n).rate i/(C*(n : ℝ)^(-beta)*(m : ℝ)^(beta+1)) ≤
      ((1/C)*(2 : ℝ)^(beta+1))*((w n).rate i*((n : ℝ)/(h : ℝ))^beta/(h : ℝ)) := by
    rw [hratio]
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hb
  apply (hm grid w hw n hn removed i q m p hm0 hcount).trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_left₀ (by positivity) hb' p
    · positivity
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)

end Luce.Section6
