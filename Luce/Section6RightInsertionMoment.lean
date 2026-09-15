import Luce.Section6DeletedSurvival
import Luce.Section6RightRemainingRate
import Luce.Section5GapReservoir

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Concrete right-endpoint insertion moment with any positive lower bound
on the number of surviving labels. The rate floor follows from the original profile. -/
theorem PowerProfile.right_deleted_insertion_moment {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ (removed : Finset (Fin n)) (i : Fin n)
      (q : Fin (Finset.univ \ removed).card) (h p : ℕ),
    0 < h → h+removed.card+q.val ≤ n →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*((w n).rate i/(C*(n : ℝ)^(-beta)*(h : ℝ)^(beta+1)))^p*
      (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*
        raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace (w n)) := by
  obtain ⟨C, hC, hfloor⟩ := hp.right_remaining_rate_floor
  refine ⟨C, hC, ?_⟩
  intro grid w hw n hn removed i q h p hh hcount
  have hW : 0 < C*(n : ℝ)^(-beta)*(h : ℝ)^(beta+1) :=
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _))
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hh) _)
  apply deleted_kernel_moment_bound_of_rate_floor (w n) removed i q p hW
  intro σ
  rw [← total_compl_deletedPrefixLabels]
  have hcard : h ≤ (Finset.univ \ deletedPrefixLabels removed σ q).card := by
    have hb := deletedPrefixLabels_card_le removed σ q
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hb : 0 < beta := hp.2.2.2.1.2.1
  apply le_trans _ (hfloor grid w hw n hn (Finset.univ \ deletedPrefixLabels removed σ q))
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow (Nat.cast_nonneg h) (Nat.cast_le.mpr hcard) (by linarith)
  · exact (mul_pos hC (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)).le

end Luce.Section6
