import Luce.Section6InactiveRightEnvelope
import Luce.Section6TerminalInactiveRight
import Luce.Section6EnvelopeMonotonicity

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- One inactive-right insertion estimate for all positive target depths in
the endpoint region. The natural gap index includes the infinite final gap. -/
theorem PowerProfile.inactive_right_all_gaps_envelope {f : ℝ → ℝ}
    {left : EndpointBehavior} {c : ℝ} (hp : PowerProfile f left (.finite c))
    (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < d ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, N ≤ n → 1 ≤ h → 16384*h ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q p : ℕ), Nat.dist q (n-h) ≤ r+1 → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*(((w n).rate i/(h : ℝ))*
        Real.exp (-d*((w n).rate i*Real.log ((n : ℝ)/(h : ℝ))))+
          Real.exp (-d*Real.sqrt ((n : ℝ)*(h : ℝ))))) := by
  obtain ⟨C1, d1, hC1, hd1, hlarge⟩ := hp.inactive_right_insertion_envelope p0 hp0
  let Q : ℕ := 10*r+10
  obtain ⟨C2, d2, N, hC2, hd2, hN, hsmall⟩ := hp.terminal_inactive_right_envelope r Q p0 hp0
  refine ⟨C1+C2, min d1 d2, N+16*r+8, by positivity, lt_min hd1 hd2, by omega, ?_⟩
  intro grid w hw n h hn hh hregion removed hremoved i q p hshift hpp hpp0
  have hi := (w n).positive i
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hhn : h ≤ n := by omega
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast hhn
  have hz : 0 ≤ (w n).rate i/(h : ℝ) := by positivity
  have hx : 0 ≤ (w n).rate i*Real.log ((n : ℝ)/(h : ℝ)) :=
    mul_nonneg hi.le (Real.log_nonneg ((one_le_div hhR).mpr hhnR))
  have hy := Real.sqrt_nonneg ((n : ℝ)*(h : ℝ))
  have hmono : ∀ A e : ℝ, 0 ≤ A → A ≤ C1+C2 → min d1 d2 ≤ e →
      ENNReal.ofReal (A*(((w n).rate i/(h : ℝ))*
        Real.exp (-e*((w n).rate i*Real.log ((n : ℝ)/(h : ℝ))))+
          Real.exp (-e*Real.sqrt ((n : ℝ)*(h : ℝ))))) ≤
      ENNReal.ofReal ((C1+C2)*(((w n).rate i/(h : ℝ))*
        Real.exp (-(min d1 d2)*((w n).rate i*Real.log ((n : ℝ)/(h : ℝ))))+
          Real.exp (-(min d1 d2)*Real.sqrt ((n : ℝ)*(h : ℝ))))) := by
    intro A e hA hAC hde
    apply ENNReal.ofReal_le_ofReal
    have h1 := insertion_envelope_mono hA hAC hde hz hx
    have h2 := insertion_envelope_mono hA hAC hde zero_le_one hy
    simp only [mul_one] at h2
    nlinarith only [h1, h2]
  by_cases hdepth : 8*r+8 ≤ h
  · have hq := (shifted_right_survivor_bounds hremoved hhn hdepth hshift).1
    have hcard : (Finset.univ \ removed).card = n-removed.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    let qf : Fin (Finset.univ \ removed).card := ⟨q, by omega⟩
    exact (hlarge grid w hw n r h (by omega) (by omega) hdepth hregion removed hremoved
      i qf p hshift hpp hpp0).trans (hmono C1 d1 hC1.le (by linarith) (min_le_left _ _))
  · have hhQ : h ≤ Q+1 := by dsimp [Q]; omega
    have hk : (Finset.univ \ removed).card ≤ q+Q := by
      have hc : (Finset.univ \ removed).card ≤ n := by
        simpa using (Finset.univ \ removed).card_le_univ
      unfold Nat.dist at hshift
      dsimp [Q]
      omega
    exact (hsmall grid w hw n h (by omega) hh hhQ removed hremoved i q p hk hpp hpp0).trans
      (hmono C2 d2 hC2.le (by linarith) (min_le_right _ _))

end Luce.Section6
