import Luce.Section6LogarithmicGapTail
import Luce.Section6SurvivalEnvelope

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

theorem logarithmic_survival_envelope {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 1)) (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x) :
    ∃ d : ℝ, 0 < d ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 8 ≤ n → 16*r ≤ n → 8*r+8 ≤ h → 16384*h ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → Nat.dist q.val (n-h) ≤ r+1 →
    (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*
      raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace (w n)) ≤
      Real.exp (-d*((w n).rate i*Real.log ((n : ℝ)/(h : ℝ))))+
        Real.exp (-d*Real.sqrt ((n : ℝ)*(h : ℝ))) := by
  obtain ⟨c, rho, hc, hrho, ht⟩ := logarithmic_gap_start_tail hf hpos
  refine ⟨min c rho, lt_min hc hrho, ?_⟩
  intro grid w hw n r h hn hr hh hsmall removed hremoved i q p hpp hshift
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast (show h ≤ n by omega)
  have hl : 0 ≤ Real.log ((n : ℝ)/(h : ℝ)) := Real.log_nonneg ((one_le_div hhR).mpr hhnR)
  have hi := (w n).positive i
  have hrate : c*((w n).rate i*Real.log ((n : ℝ)/(h : ℝ))) ≤
      (w n).rate i*(c*Real.log ((n : ℝ)/(h : ℝ))) := le_of_eq (by ring)
  exact deleted_survival_envelope_of_bounds (w n) removed i q p hpp
    (mul_nonneg hi.le hl) (Real.sqrt_nonneg _) hc.le (min_le_left _ _) (min_le_right _ _)
    hrate (ht grid w hw n r h hn hr hh hsmall removed hremoved q hshift)

end Luce.Section6
