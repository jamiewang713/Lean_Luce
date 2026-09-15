import Luce.Section6RegularCycleBounds
import Luce.Section6CriticalProfileBounds

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

theorem critical_vertex_expectation_of_rates {n : ℕ} (w : Weights n)
    (k : ℕ) (S : Finset (Fin n)) {d M : ℝ} (hd : 0 < d) (hM : 0 < M)
    (hrates : ∀ i ∈ S, d ≤ w.rate i ∧ w.rate i ≤ M) :
    (∫ clocks, (exactCycleVertexCount (raceRankPermutation clocks) (k+1) S : ℝ)
      ∂exponentialRace w) ≤ (3 : ℝ)^(k+1)*(M/d) := by
  let h : ℝ → ℝ := fun t => (M/d)*(exponentialPDF d t).toReal
  have hpdf := exponentialPDF_toReal_integrable hd
  have hpdf0 (t : ℝ) : 0 ≤ (exponentialPDF d t).toReal := ENNReal.toReal_nonneg
  have hint : (∫ t, (exponentialPDF d t).toReal) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpdf0)
      hpdf.aestronglyMeasurable]
    have he (t : ℝ) : ENNReal.ofReal (exponentialPDF d t).toReal = exponentialPDF d t :=
      ENNReal.ofReal_toReal (by simp [exponentialPDF])
    simp_rw [he]
    rw [lintegral_exponentialPDF_eq_one hd,ENNReal.toReal_one]
  have hh : Integrable h := hpdf.const_mul (M/d)
  have hi : (∫ t, h t) = M/d := by rw [integral_const_mul,hint,mul_one]
  have hdom (i : Fin n) (hiS : i ∈ S) (t : ℝ) :
      exponentialPDF (w.rate i) t ≤ ENNReal.ofReal (h t) := by
    obtain ⟨hdi,hiM⟩ := hrates i hiS
    by_cases ht : 0 ≤ t
    · rw [exponentialPDF_of_nonneg ht]
      have he : h t = M*Real.exp (-(d*t)) := by
        dsimp [h]
        rw [exponentialPDF_of_nonneg ht,ENNReal.toReal_ofReal (mul_nonneg hd.le (Real.exp_pos _).le)]
        field_simp
      rw [he]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul hiM (Real.exp_le_exp.mpr (by nlinarith))
        (Real.exp_pos _).le hM.le)
    · rw [exponentialPDF_of_neg (lt_of_not_ge ht)]
      exact bot_le
  letI : ∀ i : Fin n, IsProbabilityMeasure (volume.withDensity (exponentialPDF (w.rate i))) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  have hb := density_envelope_product (fun i => exponentialPDF (w.rate i)) S (k+1)
    (by omega) h (Filter.Eventually.of_forall (fun t => mul_nonneg (by positivity) (hpdf0 t)))
    hh (fun i hi => Filter.Eventually.of_forall (hdom i hi))
  rw [hi] at hb
  exact hb

/-- Every fixed block away from the pole contributes a bounded expected
number of cycle vertices, for each fixed cycle length. -/
theorem CriticalProfile.late_vertex_expectation {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) (k : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (S : Finset (Fin n)),
      (∀ i ∈ S, eps ≤ ((i.val : ℝ)+1)/(n : ℝ)) →
      (∫ e, (exactCycleVertexCount (raceRankPermutation e) (k+1) S : ℝ) ∂exponentialRace (w n)) ≤ C := by
  obtain ⟨a,b,ha,hb,hrates⟩ := hp.sampled_global_comparison
  refine ⟨(3 : ℝ)^(k+1)*((b/eps)/a),by positivity,?_⟩
  intro grid w hw n S hS
  apply critical_vertex_expectation_of_rates (w n) k S ha (div_pos hb heps)
  intro i hi
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hm : (0 : ℝ) < (i.val : ℝ)+1 := by positivity
  have hmn : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
  obtain ⟨hl,hu⟩ := hrates grid w hw n i
  constructor
  · apply le_trans _ hl
    apply (le_div_iff₀ hm).mpr
    exact mul_le_mul_of_nonneg_left hmn ha.le
  · apply hu.trans
    calc
      _ = b/(((i.val : ℝ)+1)/n) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left hb.le heps (hS i hi)

end Luce.Section6
