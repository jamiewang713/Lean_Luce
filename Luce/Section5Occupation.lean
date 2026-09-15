import Luce.Section5GhostCylinder
import Luce.Section4RankIntegral

/-!
# Occupation times between consecutive exponential arrivals

The integrated crossing intensity is derived from the existing exact
one-clock disintegration and the rank permutation. No spacing distribution
or conditional memoryless law is assumed. This is the quantitative gap
estimate needed for `fixed_points.tex:1219–1224`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

lemma clockBeforeCount_eq_candidate_add_background {n : ℕ}
    (clocks : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (t : ℝ) :
    clockBeforeCount clocks t = (if clocks i < t then 1 else 0) +
      clockBeforeCount (fun j => clocks (i.succAbove j)) t := by
  simpa only [clockBeforeCount, Finset.card_filter] using
    Fin.sum_univ_succAbove (fun j => if clocks j < t then (1 : ℕ) else 0) i

lemma clockBeforeCount_background_at_self {n : ℕ}
    (clocks : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    clockBeforeCount (fun j => clocks (i.succAbove j)) (clocks i) =
      clockBeforeCount clocks (clocks i) := by
  have h := clockBeforeCount_eq_candidate_add_background clocks i (clocks i)
  simpa only [lt_self_iff_false, if_false, zero_add] using h.symm

lemma measurableSet_beforeRank {n : ℕ} (i : Fin n) (k : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ | clockBeforeCount clocks (clocks i) = k} :=
  measurableSet_eq_fun
    (measurable_clockBeforeCount (fun c : Fin n → ℝ => c)
      (fun c => c i) (fun j => measurable_pi_apply j) (measurable_pi_apply i)) measurable_const

lemma measurableSet_beforeCount {n : ℕ} (t : ℝ) (k : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ | clockBeforeCount clocks t = k} :=
  measurableSet_eq_fun
    (measurable_clockBeforeCount (fun c : Fin n → ℝ => c) (fun _ => t)
      (fun j => measurable_pi_apply j) measurable_const) measurable_const

/-- Exact density of the event that label `i` has zero-based rank `k`. -/
theorem beforeRank_probability_integral {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (k : ℕ) :
    exponentialRace w {clocks | clockBeforeCount clocks (clocks i) = k} =
      ∫⁻ t, exponentialPDF (w.rate i) t *
        backgroundRace w i {background | clockBeforeCount background t = k} := by
  let A := {z : ℝ × (Fin n → ℝ) | clockBeforeCount z.2 z.1 = k}
  have hA : MeasurableSet A :=
    measurableSet_eq_fun (measurable_clockBeforeCount Prod.snd Prod.fst
      (fun j => (measurable_pi_apply j).comp measurable_snd) measurable_fst) measurable_const
  have h := exponentialRace_disintegrate w i (A.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hA)
  have hclocks : Measurable (fun clocks : Fin (n + 1) → ℝ =>
      (clocks i, fun j => clocks (i.succAbove j))) :=
    (measurable_pi_apply i).prodMk (measurable_pi_iff.mpr (fun j => measurable_pi_apply _))
  have hleft := lintegral_indicator_fun_one (μ := exponentialRace w) (hA.preimage hclocks)
  have hright (t : ℝ) := lintegral_indicator_fun_one (μ := backgroundRace w i)
    (hA.preimage (measurable_const.prodMk measurable_id :
      Measurable (fun background : Fin n → ℝ => (t, background))))
  simp only [Set.indicator_apply, Set.mem_preimage, A, Set.mem_ofPred_eq] at h hleft hright
  rw [hleft] at h
  simpa only [hright, Set.preimage_ofPred_eq, clockBeforeCount_background_at_self] using h

/-- Probability that label `i` is still present while exactly `k` clocks
have arrived. The weak survival inequality complements the strict count. -/
def survivingAtRankProbability {n : ℕ} (w : Weights n) (i : Fin n) (k : ℕ)
    (t : ℝ) : ℝ≥0∞ :=
  exponentialRace w {clocks | t ≤ clocks i ∧ clockBeforeCount clocks t = k}

lemma measurable_survivingAtRankProbability {n : ℕ} (w : Weights n)
    (i : Fin n) (k : ℕ) : Measurable (survivingAtRankProbability w i k) := by
  apply measurable_measure_prodMk_left (s := {z : ℝ × (Fin n → ℝ) |
    z.1 ≤ z.2 i ∧ clockBeforeCount z.2 z.1 = k})
  have hc : Measurable (fun z : ℝ × (Fin n → ℝ) => clockBeforeCount z.2 z.1) :=
    measurable_clockBeforeCount Prod.snd Prod.fst
      (fun j => (measurable_pi_apply j).comp measurable_snd) measurable_fst
  have hcount : MeasurableSet {z : ℝ × (Fin n → ℝ) | clockBeforeCount z.2 z.1 = k} :=
    measurableSet_eq_fun hc measurable_const
  have hsurvive : MeasurableSet {z : ℝ × (Fin n → ℝ) | z.1 ≤ z.2 i} :=
    measurableSet_le measurable_fst ((measurable_pi_apply i).comp measurable_snd)
  exact hsurvive.inter hcount

/-- Independence factors survival of the candidate and the deleted count.
This uses the actual product race, not an assumed hazard process. -/
theorem survivingAtRankProbability_eq {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (k : ℕ) (t : ℝ) :
    survivingAtRankProbability w i k t = expMeasure (w.rate i) (Ici t) *
      backgroundRace w i {background | clockBeforeCount background t = k} := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (w.rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (w.positive j)
  let A := (Ici t) ×ˢ {background : Fin n → ℝ | clockBeforeCount background t = k}
  have hA : MeasurableSet A := measurableSet_Ici.prod (measurableSet_beforeCount t k)
  have h := (measurePreserving_piFinSuccAbove (fun j => expMeasure (w.rate j)) i).measure_preimage
    hA.nullMeasurableSet
  have heq : {clocks : Fin (n + 1) → ℝ | t ≤ clocks i ∧ clockBeforeCount clocks t = k} =
      (fun clocks : Fin (n + 1) → ℝ => (clocks i, fun j => clocks (i.succAbove j))) ⁻¹' A := by
    ext clocks
    simp only [A, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Ici]
    rw [clockBeforeCount_eq_candidate_add_background clocks i t]
    by_cases ht : t ≤ clocks i
    · simp only [ht, not_lt.mpr ht, if_false, zero_add, true_and]
    · simp only [ht, false_and]
  unfold survivingAtRankProbability
  rw [heq]
  change (exponentialRace w)
    ((fun clocks : Fin (n + 1) → ℝ => (clocks i, fun j => clocks (i.succAbove j))) ⁻¹' A) =
      ((expMeasure (w.rate i)).prod (backgroundRace w i)) A at h
  exact h.trans (Measure.prod_prod _ _)

/-- The candidate's rank probability is its integrated crossing intensity,
expressed using the full race on both sides. -/
theorem beforeRank_probability_eq_intensity {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (k : ℕ) :
    exponentialRace w {clocks | clockBeforeCount clocks (clocks i) = k} =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (w.rate i) * survivingAtRankProbability w i k t := by
  rw [beforeRank_probability_integral]
  calc
    _ = ∫⁻ t, (Ici (0 : ℝ)).indicator
        (fun t => ENNReal.ofReal (w.rate i) * survivingAtRankProbability w i k t) t := by
      apply lintegral_congr
      intro t
      by_cases ht : 0 ≤ t
      · simp only [Set.indicator_apply, Set.mem_Ici, ht, if_true, exponentialPDF_of_nonneg ht,
          survivingAtRankProbability_eq, expMeasure_Ici (w.positive i) ht,
          ENNReal.ofReal_mul (w.positive i).le, mul_assoc]
      · simp only [Set.indicator_apply, Set.mem_Ici, ht, if_false,
          exponentialPDF_of_neg (lt_of_not_ge ht), zero_mul]
    _ = ∫⁻ t in Ici 0, ENNReal.ofReal (w.rate i) * survivingAtRankProbability w i k t :=
      lintegral_indicator measurableSet_Ici _
    _ = _ := by rw [restrict_Ioi_eq_restrict_Ici]

/-- Every rank has exactly one preimage, almost surely; hence the sum of
candidate rank probabilities is exactly one. -/
theorem sum_beforeRank_probability {n : ℕ} (w : Weights n) (k : ℕ) (hk : k < n) :
    (∑ i, exponentialRace w {clocks | clockBeforeCount clocks (clocks i) = k}) = 1 := by
  rw [sum_measures_eq_lintegral_count _ _ _ (fun i _ => measurableSet_beforeRank i k)]
  calc
    _ = ∫⁻ _clocks : Fin n → ℝ, (1 : ℝ≥0∞) ∂exponentialRace w := by
      apply lintegral_congr_ae
      filter_upwards [exponentialRace_injective_ae w] with clocks hc
      let R := rankPermutation clocks hc
      let j : Fin n := ⟨k, hk⟩
      norm_cast
      apply Finset.card_eq_one.mpr
      refine ⟨R.symm j, ?_⟩
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      change (R i).val = j.val ↔ i = R.symm j
      rw [← Fin.ext_iff]
      exact R.eq_symm_apply.symm
    _ = 1 := by simp

/-- Integrated crossing intensity at any existing rank is exactly one.
This is the rigorous hazard normalization behind the spacing estimate. -/
theorem integrated_rank_crossing_intensity {n : ℕ} (w : Weights (n + 1))
    (k : ℕ) (hk : k < n + 1) :
    (∫⁻ t in Ioi 0, ∑ i, ENNReal.ofReal (w.rate i) *
      survivingAtRankProbability w i k t) = 1 := by
  rw [lintegral_finsetSum]
  · simp_rw [← beforeRank_probability_eq_intensity]
    exact sum_beforeRank_probability w k hk
  · intro i _
    exact measurable_const.mul (measurable_survivingAtRankProbability w i k)

/-- Deterministic reservoir input, at a single rank. The hypothesis is a
lower bound on the rate of every possible remaining label set, not an
assumed bound on a random spacing or its expectation. -/
lemma remaining_rate_lower_pointwise {n : ℕ} (w : Weights n) (k : ℕ) (B : ℝ)
    (hremaining : ∀ s : Finset (Fin n), s.card = n - k → B ≤ w.total s)
    (t : ℝ) (clocks : Fin n → ℝ) :
    ENNReal.ofReal B * (if clockBeforeCount clocks t = k then 1 else 0) ≤
      ∑ i, ENNReal.ofReal (w.rate i) *
        (if t ≤ clocks i ∧ clockBeforeCount clocks t = k then 1 else 0) := by
  by_cases hk : clockBeforeCount clocks t = k
  · let s := Finset.univ.filter (fun i => t ≤ clocks i)
    have hcard : s.card = n - k := by
      have hp := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i : Fin n => clocks i < t)
      have hp' : clockBeforeCount clocks t + s.card = n := by
        simpa only [clockBeforeCount, s, not_lt, Finset.card_univ, Fintype.card_fin] using hp
      omega
    have hb := hremaining s hcard
    simp only [hk, if_true, and_true, mul_one, mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    change ENNReal.ofReal B ≤ ∑ i ∈ s, ENNReal.ofReal (w.rate i)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (w.positive i).le)]
    exact ENNReal.ofReal_le_ofReal hb
  · simp only [hk, if_false, and_false, mul_zero, Finset.sum_const_zero, le_refl]

/-- Integrating the deterministic rate bound over the actual race gives
the lower bound on its rank-crossing intensity. -/
theorem beforeCount_probability_mul_le_intensity {n : ℕ} (w : Weights n)
    (k : ℕ) (B : ℝ)
    (hremaining : ∀ s : Finset (Fin n), s.card = n - k → B ≤ w.total s) (t : ℝ) :
    ENNReal.ofReal B * exponentialRace w {clocks | clockBeforeCount clocks t = k} ≤
      ∑ i, ENNReal.ofReal (w.rate i) * survivingAtRankProbability w i k t := by
  let E := {clocks : Fin n → ℝ | clockBeforeCount clocks t = k}
  let F := fun i : Fin n => {clocks : Fin n → ℝ | t ≤ clocks i ∧ clockBeforeCount clocks t = k}
  have hE : MeasurableSet E := measurableSet_beforeCount t k
  have hF (i : Fin n) : MeasurableSet (F i) :=
    (measurableSet_le measurable_const (measurable_pi_apply i)).inter hE
  have hEint : (∫⁻ clocks, (if clockBeforeCount clocks t = k then (1 : ℝ≥0∞) else 0)
      ∂exponentialRace w) = exponentialRace w E := by
    simpa only [Set.indicator_apply, E, Set.mem_ofPred_eq] using
      lintegral_indicator_fun_one (μ := exponentialRace w) hE
  have hFint (i : Fin n) : (∫⁻ clocks, ENNReal.ofReal (w.rate i) *
      (if t ≤ clocks i ∧ clockBeforeCount clocks t = k then (1 : ℝ≥0∞) else 0)
      ∂exponentialRace w) = ENNReal.ofReal (w.rate i) * survivingAtRankProbability w i k t := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    simpa only [Set.indicator_apply, F, Set.mem_ofPred_eq, survivingAtRankProbability] using
      lintegral_indicator_fun_one (μ := exponentialRace w) (hF i)
  calc
    _ = ∫⁻ clocks, ENNReal.ofReal B *
        (if clockBeforeCount clocks t = k then (1 : ℝ≥0∞) else 0) ∂exponentialRace w := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hEint]
    _ ≤ ∫⁻ clocks, ∑ i, ENNReal.ofReal (w.rate i) *
        (if t ≤ clocks i ∧ clockBeforeCount clocks t = k then (1 : ℝ≥0∞) else 0)
        ∂exponentialRace w :=
      lintegral_mono (remaining_rate_lower_pointwise w k B hremaining t)
    _ = _ := by
      rw [lintegral_finsetSum]
      · simp_rw [hFint]
      · intro i _
        exact measurable_const.mul (Measurable.ite (hF i) measurable_const measurable_const)

/-- Expected time spent with exactly `k` arrivals, obtained from the proved
crossing identity and a deterministic positive remaining-rate bound. -/
theorem beforeCount_occupation_le {n : ℕ} (w : Weights (n + 1))
    (k : ℕ) (hk : k < n + 1) (B : ℝ) (hB : 0 < B)
    (hremaining : ∀ s : Finset (Fin (n + 1)), s.card = (n + 1) - k → B ≤ w.total s) :
    (∫⁻ t in Ioi 0, exponentialRace w {clocks | clockBeforeCount clocks t = k}) ≤
      ENNReal.ofReal (1 / B) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos hB]
  apply ENNReal.le_inv_iff_mul_le.mpr
  rw [mul_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ∫⁻ t in Ioi 0, ∑ i, ENNReal.ofReal (w.rate i) *
        survivingAtRankProbability w i k t :=
      lintegral_mono (beforeCount_probability_mul_le_intensity w k B hremaining)
    _ = 1 := integrated_rank_crossing_intensity w k hk

end Luce
