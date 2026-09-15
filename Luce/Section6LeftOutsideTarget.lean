import Luce.Section6LeftOutsideShiftedLp

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The outside-left ordinary kernel is O(1/n) when the source rate is
bounded. The concrete profile theorem supplies this rate bound. -/
theorem left_bounded_source_kernel_le_inverse_row {n h a t M d : ℝ}
    (hn : 0 < n) (hh : 0 < h) (hhn : h ≤ n) (ha : 1 ≤ a)
    (ht : 0 ≤ t) (htM : t ≤ M) (hd : 0 ≤ d) :
    (t*(h/n)^a/h)*Real.exp (-d*(t*(h/n)^a)) ≤ M/n := by
  have hx : 0 < h/n := div_pos hh hn
  have hx1 : h/n ≤ 1 := (div_le_one hn).mpr hhn
  have hp : (h/n)^a ≤ h/n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hx hx1 ha
  have he : Real.exp (-d*(t*(h/n)^a)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) (by positivity))
  have hz : 0 ≤ t*(h/n)^a/h := by positivity
  calc
    _ ≤ t*(h/n)^a/h := by simpa using mul_le_mul_of_nonneg_left he hz
    _ ≤ t*(h/n)/h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp ht) hh.le
    _ = t/n := by field_simp
    _ ≤ M/n := div_le_div_of_nonneg_right htM hn.le

/-- Source-uniform inverse-row norm bound outside the left source block.
The rate upper bound is derived, not an input. -/
theorem PowerProfile.left_outside_insertion_target_bound {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (p0 : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ sigma ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 0 < n → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) ≤ delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    Nat.dist q.val (h-1) ≤ r+1 → sigma ≤ ((i.val : ℝ)+1)/(n : ℝ) →
    1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C/(n : ℝ)) := by
  obtain ⟨B, d, delta, hB, hd, hdelta, hds, hb⟩ := hp.left_outside_shifted_insertion_Lp hsigma hsigma1 p0
  obtain ⟨M, hM, hrate⟩ := hp.sampled_upper_outside_left hsigma hsigma1
  refine ⟨B*M, delta, mul_pos hB hM, hdelta, hds, ?_⟩
  intro grid w hw n r h hn hh hsmall removed hremoved i q p hshift hi hpp hpp0
  apply (hb grid w hw n r h hn hh hsmall removed hremoved i q p hshift hi hpp hpp0).trans
  apply ENNReal.ofReal_le_ofReal
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hhn : (h : ℝ) ≤ n := (div_le_one hnR).mp
    ((hsmall.trans hds).trans hsigma1.le)
  have he := left_bounded_source_kernel_le_inverse_row hnR hhR hhn hp.2.2.1.2.1.le
    ((w n).positive i).le (hrate grid w hw n i hi) hd.le
  have hm := mul_le_mul_of_nonneg_left he hB.le
  simpa only [mul_assoc, mul_div_assoc] using hm

end Luce.Section6
