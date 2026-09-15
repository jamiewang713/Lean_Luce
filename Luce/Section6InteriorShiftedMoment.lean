import Luce.Section6InteriorInsertionMoment
import Luce.Section6InteriorGapTail
import Luce.Section6InteriorGapBounds

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Interior-target insertion moments for every source, with the demanded
rank shifts and deletion margins discharged from the original profile. -/
theorem PowerProfile.interior_shifted_insertion_moment {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r : ℕ) :
    ∃ B d N : ℝ, 0 < B ∧ 0 < d ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → N ≤ (n : ℝ) →
    eps*(n : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ (1-eps)*(n : ℝ) →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    Nat.dist q.val (h-1) ≤ r+1 → 1 ≤ p →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*(B*((w n).rate i/(n : ℝ)))^p*
        (Real.exp (-d*(w n).rate i)+Real.exp (-d*(n : ℝ))) := by
  obtain ⟨C, hC, hmoment⟩ := hp.interior_deleted_insertion_moment (half_pos heps)
  obtain ⟨d, Ns, hd, hNs, hsurvival⟩ := hp.interior_survival_envelope (half_pos heps)
  refine ⟨1/C, d, max Ns ((8*(r : ℝ)+8)/eps), one_div_pos.mpr hC, hd,
    hNs.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n h hn hlarge hl hu removed hremoved i q p hshift hpp
  have hi := (w n).positive i
  have hmargin : 8*(r : ℝ)+8 ≤ eps*(n : ℝ) := by
    have hh := (le_max_right Ns ((8*(r : ℝ)+8)/eps)).trans hlarge
    have hh' := (div_le_iff₀ heps).mp hh
    nlinarith
  obtain ⟨hqlo, hqhi⟩ := shifted_interior_gap_bounds removed hremoved q hmargin hl hu hshift
  have hm := hmoment grid w hw n hn removed i q p hqhi
  have hs := hsurvival grid w hw n hn ((le_max_left _ _).trans hlarge) removed i q p hqlo hpp
  have he : (w n).rate i/(C*(n : ℝ)) = (1/C)*((w n).rate i/(n : ℝ)) := by ring
  rw [he] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end Luce.Section6
