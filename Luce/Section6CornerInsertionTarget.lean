import Luce.Section6EndpointEnvelopeTarget
import Luce.Section6InsertionLpEnvelope

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Actual right-corner insertion norms have inverse target-depth maxima. -/
theorem PowerProfile.right_corner_insertion_target_bound {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C H delta : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ i : Fin n, (terminalDepth i : ℝ)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
    Nat.dist q.val (n-h) ≤ r+1 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C/(h : ℝ)) := by
  obtain ⟨B, d, nu, H, delta, hB, hd, hnu, hH, hdelta, hdelta1, hb⟩ :=
    hp.right_insertion_Lp_envelope r p0 hp0 1 zero_lt_one le_rfl
  obtain ⟨D, hD, hbound⟩ := endpoint_envelope_target_bound hp.2.2.2.1.2.1 zero_lt_one hd hnu
  refine ⟨B*D, max H 1, delta, mul_pos hB hD, hH.trans_le (le_max_left _ _), hdelta, hdelta1, ?_⟩
  intro grid w hw n h hn hh hsmall removed hremoved i hi q p hpp hpp0 hshift
  have hh1 : 1 ≤ h := by exact_mod_cast (le_max_right H 1).trans hh
  have he := hb grid w hw n h hn ((le_max_left _ _).trans hh) hsmall removed hremoved i hi q p hpp hpp0 hshift
  have ht := (hbound (terminalDepth i) h (((terminalDepth i : ℝ)/(h : ℝ))^beta)
    (terminalDepth_pos i) hh1).1
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  have hm := mul_le_mul_of_nonneg_left ht hB.le
  simpa only [exceptionalEnvelope, mul_div_assoc] using hm

/-- Actual left-corner insertion norms have inverse target-depth maxima. -/
theorem PowerProfile.left_corner_insertion_target_bound {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C H delta : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ i : Fin n, ((i.val : ℝ)+1)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
    Nat.dist q.val (h-1) ≤ r+1 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C/(h : ℝ)) := by
  obtain ⟨B, d, nu, H, delta, hB, hd, hnu, hH, hdelta, hdelta1, hb⟩ :=
    hp.left_insertion_Lp_envelope r p0 hp0 1 zero_lt_one le_rfl
  have halpha : 0 < alpha := zero_lt_one.trans hp.2.2.1.2.1
  obtain ⟨D, hD, hbound⟩ := endpoint_envelope_target_bound halpha zero_lt_one hd hnu
  refine ⟨B*D, max H 1, delta, mul_pos hB hD, hH.trans_le (le_max_left _ _), hdelta, hdelta1, ?_⟩
  intro grid w hw n h hn hh hsmall removed hremoved i hi q p hpp hpp0 hshift
  have hh1 : 1 ≤ h := by exact_mod_cast (le_max_right H 1).trans hh
  have he := hb grid w hw n h hn ((le_max_left _ _).trans hh) hsmall removed hremoved i hi q p hpp hpp0 hshift
  have ht := (hbound (i.val+1) h (((h : ℝ)/((i.val : ℝ)+1))^alpha) (by omega) hh1).2
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  have hm := mul_le_mul_of_nonneg_left ht hB.le
  simpa only [exceptionalEnvelope, Nat.cast_add, Nat.cast_one, min_comm, mul_div_assoc] using hm

end Luce.Section6
