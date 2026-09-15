import Luce.Section6InteriorEnvelope

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Both terms in the middle envelope have a uniform inverse-row bound. -/
theorem interior_envelope_le_inverse_row {d n : ℝ} (hd : 0 < d) (hn : 0 < n)
    (x : ℝ) :
    (x/n)*Real.exp (-d*x)+Real.exp (-d*n) ≤ (2*Real.exp (-1)/d)/n := by
  have hx : x*Real.exp (-d*x) ≤ Real.exp (-1)/d := by
    simpa [rateKernel, survivalKernel] using rateKernel_le_exp_neg_one_div (a := x) hd
  have hy : n*Real.exp (-d*n) ≤ Real.exp (-1)/d := by
    simpa [rateKernel, survivalKernel] using rateKernel_le_exp_neg_one_div (a := n) hd
  apply (le_div_iff₀ hn).mpr
  have he : ((x/n)*Real.exp (-d*x)+Real.exp (-d*n))*n =
      x*Real.exp (-d*x)+n*Real.exp (-d*n) := by field_simp
  rw [he]
  rw [mul_div_assoc]
  linarith

/-- Summing any subset of a row or column of the middle comparison kernel
is bounded independently of n. Constant x gives rows; sampled rates give columns. -/
theorem interior_envelope_sum_bound {d : ℝ} (hd : 0 < d) {n : ℕ} (hn : 0 < n)
    (s : Finset (Fin n)) (x : Fin n → ℝ) :
    (∑ i ∈ s, (((x i)/(n : ℝ))*Real.exp (-d*x i)+Real.exp (-d*(n : ℝ)))) ≤
      2*Real.exp (-1)/d := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : (s.card : ℝ) ≤ n := by
    have hh : s.card ≤ n := by simpa using s.card_le_univ
    exact_mod_cast hh
  have hb : 0 ≤ (2*Real.exp (-1)/d)/(n : ℝ) := by positivity
  calc
    _ ≤ ∑ _i ∈ s, (2*Real.exp (-1)/d)/(n : ℝ) :=
      Finset.sum_le_sum (fun i _ => interior_envelope_le_inverse_row hd hnR (x i))
    _ = (s.card : ℝ)*((2*Real.exp (-1)/d)/(n : ℝ)) := by simp
    _ ≤ (n : ℝ)*((2*Real.exp (-1)/d)/(n : ℝ)) := mul_le_mul_of_nonneg_right hc hb
    _ = _ := by field_simp

/-- Uniform over every source, with no upper bound on its rate assumed. -/
theorem PowerProfile.interior_insertion_target_bound {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → N ≤ (n : ℝ) →
    eps*(n : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ (1-eps)*(n : ℝ) →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    Nat.dist q.val (h-1) ≤ r+1 → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C/(n : ℝ)) := by
  obtain ⟨B, d, N, hB, hd, hN, hb⟩ := hp.interior_insertion_envelope heps r p0 hp0
  refine ⟨B*(2*Real.exp (-1)/d), N, by positivity, hN, ?_⟩
  intro grid w hw n h hn hlarge hl hu removed hremoved i q p hshift hpp hpp0
  apply (hb grid w hw n h hn hlarge hl hu removed hremoved i q p hshift hpp hpp0).trans
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left
    (interior_envelope_le_inverse_row hd (Nat.cast_pos.mpr hn) ((w n).rate i)) hB.le
  simpa only [mul_div_assoc] using hh

end Luce.Section6
