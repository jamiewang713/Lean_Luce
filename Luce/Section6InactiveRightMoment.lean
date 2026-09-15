import Luce.Section6InactiveBounds
import Luce.Section6DeletedSurvival
import Luce.Section6GapOffsets
import Luce.Section5GapReservoir

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Inactive-right moments with the rate floor derived from the original
finite positive endpoint limit and actual remaining-label cardinality. -/
theorem PowerProfile.inactive_right_shifted_moment {f : ℝ → ℝ}
    {left : EndpointBehavior} {c : ℝ} (hp : PowerProfile f left (.finite c)) :
    ∃ B : ℝ, 0 < B ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 0 < n → h ≤ n → 8*r+8 ≤ h →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    Nat.dist q.val (n-h) ≤ r+1 →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*(B*((w n).rate i/(h : ℝ)))^p*
      (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*
        raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace (w n)) := by
  obtain ⟨d, hd, hlower⟩ := hp.global_lower_of_right_finite
  refine ⟨2/d, by positivity, ?_⟩
  intro grid w hw n r h hn hhn hh removed hremoved i q p hshift
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hW : 0 < (d/2)*(h : ℝ) := by positivity
  have hfloor : ∀ σ, (d/2)*(h : ℝ) ≤ orderedRemainingRate (compactDeletedWeights (w n) removed) σ q := by
    intro σ
    rw [← total_compl_deletedPrefixLabels]
    have hg := (shifted_right_survivor_bounds hremoved hhn hh hshift).2.1
    have hprefix := deletedPrefixLabels_card_le removed σ q
    have hc : h ≤ 2*(Finset.univ \ deletedPrefixLabels removed σ q).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    have hcR : (h : ℝ) ≤ 2*((Finset.univ \ deletedPrefixLabels removed σ q).card : ℝ) := by exact_mod_cast hc
    calc
      _ ≤ d*((Finset.univ \ deletedPrefixLabels removed σ q).card : ℝ) := by nlinarith
      _ = ∑ _j ∈ Finset.univ \ deletedPrefixLabels removed σ q, d := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => by rw [hw n j]; exact hlower _ (samplePoint_mem grid j))
  have he := deleted_kernel_moment_bound_of_rate_floor (w n) removed i q p hW hfloor
  have hid : (w n).rate i/((d/2)*(h : ℝ)) = (2/d)*((w n).rate i/(h : ℝ)) := by
    field_simp
  simpa only [hid] using he

end Luce.Section6
