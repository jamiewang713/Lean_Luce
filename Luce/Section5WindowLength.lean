import Luce.Section5Occupation
import Mathlib.Order.Interval.Finset.Nat

/-!
# Expected lengths of interior ghost windows

The finite consequence of the reservoir argument in
`fixed_points.tex:1219–1224`. The only auxiliary hypothesis is an explicit
deterministic lower bound on the total rate of every possible remaining set.
The expected spacing estimate is proved in `Section5Occupation`, rather
than assumed. Tonelli then sums the at most `2 * ell + 1` occupied levels.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

/-- Lebesgue measure of the paper's open window `J_j`. The zero extension
at tied backgrounds is on a proved null set under the exponential race. -/
def ghostWindowVolume {n : ℕ} (ell : ℕ) (old : Fin n → ℝ) (j : Fin n) : ℝ≥0∞ :=
  if h : Function.Injective old then volume {t | GhostWindowByOrder old h ell j t} else 0

/-- Real length; finiteness is proved below before using its expectation. -/
def ghostWindowLength {n : ℕ} (ell : ℕ) (old : Fin n → ℝ) (j : Fin n) : ℝ :=
  (ghostWindowVolume ell old j).toReal

lemma ghostWindowVolume_eq_count {n : ℕ} (ell : ℕ) (old : Fin n → ℝ)
    (hinj : Injective old) (hnonneg : ∀ i, 0 ≤ old i) (j : Fin n) :
    ghostWindowVolume ell old j = volume {t | GhostCountWindow ell old j t} := by
  simp only [ghostWindowVolume, hinj, dite_true]
  apply measure_congr
  have havoid : ∀ᵐ t ∂volume, ∀ i, t ≠ old i :=
    ae_all_iff.mpr (fun i => Measure.ae_ne volume (old i))
  filter_upwards [havoid] with t ht
  exact propext (ghostWindowByOrder_iff_count old hinj hnonneg ell j t ht)

lemma measurable_ghostCountWindowVolume {n : ℕ} (ell : ℕ) (j : Fin n) :
    Measurable (fun old : Fin n → ℝ => volume {t | GhostCountWindow ell old j t}) := by
  apply measurable_measure_prodMk_left (s :=
    {z : (Fin n → ℝ) × ℝ | GhostCountWindow ell z.1 j z.2})
  exact measurableSet_ghostCountWindow ell Prod.fst j Prod.snd
    (fun i => (measurable_pi_apply i).comp measurable_fst) measurable_snd

lemma ghostWindowVolume_ae_eq_count {n : ℕ} (w : Weights n) (ell : ℕ) (j : Fin n) :
    (fun old => ghostWindowVolume ell old j) =ᵐ[exponentialRace w]
      (fun old => volume {t | GhostCountWindow ell old j t}) := by
  filter_upwards [exponentialRace_injective_ae w,
    exponentialRace_nonnegative_background w] with old hi hn
  exact ghostWindowVolume_eq_count ell old hi hn j

lemma aemeasurable_ghostWindowVolume {n : ℕ} (w : Weights n) (ell : ℕ) (j : Fin n) :
    AEMeasurable (fun old => ghostWindowVolume ell old j) (exponentialRace w) :=
  (measurable_ghostCountWindowVolume ell j).aemeasurable.congr
    (ghostWindowVolume_ae_eq_count w ell j).symm

/-- Tonelli for the actual order-statistic interval. -/
theorem ghostWindowVolume_expectation_eq {n : ℕ} (w : Weights n) (ell : ℕ) (j : Fin n) :
    (∫⁻ old, ghostWindowVolume ell old j ∂exponentialRace w) =
      ∫⁻ t, exponentialRace w {old | GhostCountWindow ell old j t} := by
  rw [lintegral_congr_ae (ghostWindowVolume_ae_eq_count w ell j)]
  let A := {z : (Fin n → ℝ) × ℝ | GhostCountWindow ell z.1 j z.2}
  have hA : MeasurableSet A :=
    measurableSet_ghostCountWindow ell Prod.fst j Prod.snd
      (fun i => (measurable_pi_apply i).comp measurable_fst) measurable_snd
  exact (Measure.prod_apply hA).symm.trans (Measure.prod_apply_symm hA)

lemma measurable_beforeCount_probability {n : ℕ} (w : Weights n) (k : ℕ) :
    Measurable (fun t : ℝ => exponentialRace w {old | clockBeforeCount old t = k}) := by
  apply measurable_measure_prodMk_left (s :=
    {z : ℝ × (Fin n → ℝ) | clockBeforeCount z.2 z.1 = k})
  exact measurableSet_eq_fun (measurable_clockBeforeCount Prod.snd Prod.fst
    (fun i => (measurable_pi_apply i).comp measurable_snd) measurable_fst) measurable_const

/-- Only ranks between the two window endpoints can be occupied. -/
lemma ghostCountWindow_probability_le_rank_sum {n : ℕ} (w : Weights n)
    (ell : ℕ) (j : Fin n) (t : ℝ) :
    exponentialRace w {old | GhostCountWindow ell old j t} ≤
      (Ioi 0).indicator (fun t => ∑ k ∈ Finset.Icc (j.val - ell) (j.val + ell),
        exponentialRace w {old | clockBeforeCount old t = k}) t := by
  by_cases ht : 0 < t
  · simp only [Set.indicator_apply, Set.mem_Ioi, ht, if_true]
    calc
      _ ≤ exponentialRace w
          (⋃ k ∈ Finset.Icc (j.val - ell) (j.val + ell),
            {old | clockBeforeCount old t = k}) := by
        apply measure_mono
        intro old ho
        obtain ⟨_, hlo, hhi⟩ := ho
        exact Set.mem_iUnion.mpr ⟨clockBeforeCount old t,
          Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩⟩
      _ ≤ _ := measure_biUnion_finset_le _ _
  · have hzero : {old : Fin n → ℝ | GhostCountWindow ell old j t} = ∅ := by
      ext old
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => ht h.1
    simp only [hzero, measure_empty, Set.indicator_apply, Set.mem_Ioi, ht, if_false, le_refl]

/-- Finite interior-window estimate. All reservoir information appears in
`hremaining`; no conditional spacing law or expectation is a hypothesis. -/
theorem ghostWindowVolume_expectation_le {n : ℕ} (w : Weights (n + 1))
    (ell : ℕ) (j : Fin (n + 1)) (hj : j.val + ell < n + 1)
    (B : ℝ) (hB : 0 < B)
    (hremaining : ∀ k, k ≤ j.val + ell → ∀ s : Finset (Fin (n + 1)),
      s.card = (n + 1) - k → B ≤ w.total s) :
    (∫⁻ old, ghostWindowVolume ell old j ∂exponentialRace w) ≤
      ENNReal.ofReal ((2 * ell + 1 : ℕ) / B) := by
  let K := Finset.Icc (j.val - ell) (j.val + ell)
  have hcard : K.card ≤ 2 * ell + 1 := by
    dsimp [K]
    rw [Nat.card_Icc]
    omega
  calc
    _ = ∫⁻ t, exponentialRace w {old | GhostCountWindow ell old j t} :=
      ghostWindowVolume_expectation_eq w ell j
    _ ≤ ∫⁻ t, (Ioi 0).indicator (fun t => ∑ k ∈ K,
        exponentialRace w {old | clockBeforeCount old t = k}) t :=
      lintegral_mono (ghostCountWindow_probability_le_rank_sum w ell j)
    _ = ∑ k ∈ K, ∫⁻ t in Ioi 0,
        exponentialRace w {old | clockBeforeCount old t = k} := by
      rw [lintegral_indicator measurableSet_Ioi, lintegral_finsetSum]
      exact fun k _ => measurable_beforeCount_probability w k
    _ ≤ ∑ _k ∈ K, ENNReal.ofReal (1 / B) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := (Finset.mem_Icc.mp hk).2
      exact beforeCount_occupation_le w k (lt_of_le_of_lt hk' hj) B hB
        (hremaining k hk')
    _ = (K.card : ℝ≥0∞) * ENNReal.ofReal (1 / B) := by simp
    _ ≤ ((2 * ell + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / B) := by
      gcongr
    _ = ENNReal.ofReal ((2 * ell + 1 : ℕ) / B) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- The actual length is integrable; the preceding finite bound rules out
using totalized `toReal` to conceal infinite intervals. -/
theorem ghostWindowLength_integrable {n : ℕ} (w : Weights (n + 1))
    (ell : ℕ) (j : Fin (n + 1)) (hj : j.val + ell < n + 1)
    (B : ℝ) (hB : 0 < B)
    (hremaining : ∀ k, k ≤ j.val + ell → ∀ s : Finset (Fin (n + 1)),
      s.card = (n + 1) - k → B ≤ w.total s) :
    Integrable (fun old => ghostWindowLength ell old j) (exponentialRace w) := by
  apply integrable_toReal_of_lintegral_ne_top (aemeasurable_ghostWindowVolume w ell j)
  exact ne_of_lt ((ghostWindowVolume_expectation_le w ell j hj B hB hremaining).trans_lt
    ENNReal.ofReal_lt_top)

/-- Real-valued expected length of the paper's interval, with the exact
finite reservoir assumptions exposed. -/
theorem ghostWindowLength_expectation_le {n : ℕ} (w : Weights (n + 1))
    (ell : ℕ) (j : Fin (n + 1)) (hj : j.val + ell < n + 1)
    (B : ℝ) (hB : 0 < B)
    (hremaining : ∀ k, k ≤ j.val + ell → ∀ s : Finset (Fin (n + 1)),
      s.card = (n + 1) - k → B ≤ w.total s) :
    (∫ old, ghostWindowLength ell old j ∂exponentialRace w) ≤
      (2 * ell + 1 : ℕ) / B := by
  have hm := aemeasurable_ghostWindowVolume w ell j
  have hb := ghostWindowVolume_expectation_le w ell j hj B hB hremaining
  have hf := ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top)
  change (∫ old, (ghostWindowVolume ell old j).toReal ∂exponentialRace w) ≤ _
  rw [integral_toReal hm (ae_lt_top' hm hf)]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * ell + 1 : ℕ) / B)] using h

end Luce
