import Luce.Section6DeletedSurvival
import Luce.Section6LeftRemainingRate
import Luce.Section5GapReservoir

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Concrete left-endpoint moment reduction before substituting the sampled
marked-rate asymptotic. The chain-uniform rate floor is proved from PowerProfile. -/
theorem PowerProfile.left_deleted_insertion_moment {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ C eps : ℝ, 0 < C ∧ 0 < eps ∧ eps < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 0 < n → ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    4*r+4 ≤ q.val → (q.val : ℝ) ≤ eps*(n : ℝ)/4 →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*((w n).rate i/(C*(n : ℝ)^alpha*(q.val : ℝ)^(1-alpha)))^p*
      (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*
        raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace (w n)) := by
  obtain ⟨C, eps, hC, heps, heps1, hfloor⟩ := hp.left_remaining_rate_floor_bounded_displacement
  refine ⟨C, eps, hC, heps, heps1, ?_⟩
  intro grid w hw n r hn removed hremoved i q p hq hqn
  have hqpos : (0 : ℝ) < q.val := Nat.cast_pos.mpr (by omega)
  have hW : 0 < C*(n : ℝ)^alpha*(q.val : ℝ)^(1-alpha) :=
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _))
      (Real.rpow_pos_of_pos hqpos _)
  apply deleted_kernel_moment_bound_of_rate_floor (w n) removed i q p hW
  intro σ
  rw [← total_compl_deletedPrefixLabels]
  apply hfloor grid w hw n q.val r hn hq hqn
  exact (deletedPrefixLabels_card_le removed σ q).trans (by omega)

end Luce.Section6
