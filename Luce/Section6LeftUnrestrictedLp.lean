import Luce.Section6LeftInsertionMoment
import Luce.Section6UniformMomentDecay

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

theorem deleted_survival_integral_le_one {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n)
    (q : Fin (Finset.univ \ removed).card) (p : ℕ) :
    (∫ old, Real.exp (-((p : ℝ)*w.rate i*
      raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace w) ≤ 1 := by
  have hb : (fun old => Real.exp (-((p : ℝ)*w.rate i*
      raceGapStart (compactDeletedClocks removed old) q))) ≤ᵐ[exponentialRace w] (fun _ => (1 : ℝ)) := by
    filter_upwards [exponentialRace_injective_ae w, exponentialRace_nonnegative_background w]
      with old hi hn
    have hc := compactDeletedClocks_injective removed old hi
    have hs : 0 ≤ raceGapStart (compactDeletedClocks removed old) q := by
      rw [raceGapStart_eq_consecutiveGapLower _ hc]
      exact consecutiveGapLower_nonneg _ hc (fun k => hn _) q
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (w.positive i).le) hs))
  simpa using integral_mono_ae (deleted_survival_integrable w removed i q p) (integrable_const 1) hb

/-- The left rate-floor norm estimate before restricting the source label.
Every moment and survival premise is discharged from the original model. -/
theorem PowerProfile.left_unrestricted_insertion_Lp {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (p0 : ℕ) :
    ∃ C eps : ℝ, 0 < C ∧ 0 < eps ∧ eps < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 0 < n → ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    4*r+4 ≤ q.val → (q.val : ℝ) ≤ eps*(n : ℝ)/4 → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal ((2*(p0.factorial : ℝ))*((w n).rate i/
        (C*(n : ℝ)^alpha*(q.val : ℝ)^(1-alpha)))) := by
  obtain ⟨C, eps, hC, heps, heps1, hm⟩ := hp.left_deleted_insertion_moment
  refine ⟨C, eps, hC, heps, heps1, ?_⟩
  intro grid w hw n r hn removed hremoved i q p hq hqn hpp hpp0
  have hi := (w n).positive i
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hqR : (0 : ℝ) < q.val := Nat.cast_pos.mpr (by omega)
  have hz : 0 ≤ (w n).rate i/(C*(n : ℝ)^alpha*(q.val : ℝ)^(1-alpha)) := by positivity
  apply deleted_kernel_eLpNorm_le_of_moment (w n) removed i q.val p (by omega) (by positivity)
  have hh := (hm grid w hw n r hn removed hremoved i q p hq hqn).trans
    (mul_le_mul_of_nonneg_left (deleted_survival_integral_le_one (w n) removed i q p) (by positivity))
  simp only [mul_one] at hh
  have hd := uniform_moment_decay hpp hpp0 (B := 1) (z := (w n).rate i/
      (C*(n : ℝ)^alpha*(q.val : ℝ)^(1-alpha))) (d := 0) (x := 0)
      zero_le_one hz (le_refl 0) (le_refl 0)
  simp only [one_mul, neg_zero, zero_mul, Real.exp_zero, mul_one, zero_div] at hd
  apply hh.trans
  apply le_trans ?_ hd
  nlinarith [pow_nonneg hz p, Nat.cast_nonneg (α := ℝ) p.factorial]

end Luce.Section6
