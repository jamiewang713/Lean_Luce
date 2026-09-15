import Luce.Section6InteriorRemainingRate
import Luce.Section6DeletedSurvival
import Luce.Section5GapReservoir

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- A macroscopic number of unmarked survivors supplies the actual
remaining-rate floor for every elimination order. -/
theorem PowerProfile.interior_deleted_insertion_moment {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ (removed : Finset (Fin n)) (i : Fin n)
      (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    eps*(n : ℝ) ≤ ((Finset.univ \ removed).card : ℝ)-(q.val : ℝ) →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*((w n).rate i/(C*(n : ℝ)))^p*
      (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*raceGapStart (compactDeletedClocks removed old) q))
        ∂exponentialRace (w n)) := by
  obtain ⟨C, hC, hfloor⟩ := hp.interior_remaining_rate heps
  refine ⟨C, hC, ?_⟩
  intro grid w hw n hn removed i q p hsurv
  apply deleted_kernel_moment_bound_of_rate_floor (w n) removed i q p
    (mul_pos hC (Nat.cast_pos.mpr hn))
  intro σ
  rw [← total_compl_deletedPrefixLabels]
  apply hfloor grid w hw n hn (Finset.univ \ deletedPrefixLabels removed σ q)
  have hcount : (Finset.univ \ removed).card-q.val ≤
      (Finset.univ \ deletedPrefixLabels removed σ q).card := by
    have hh := deletedPrefixLabels_card_le removed σ q
    simp only [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hcountR : (((Finset.univ \ removed).card-q.val : ℕ) : ℝ) ≤
      ((Finset.univ \ deletedPrefixLabels removed σ q).card : ℝ) := Nat.cast_le.mpr hcount
  rw [Nat.cast_sub q.isLt.le] at hcountR
  exact hsurv.trans hcountR

end Luce.Section6
