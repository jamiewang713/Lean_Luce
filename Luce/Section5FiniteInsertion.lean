import Luce.Section5WindowProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The finite insertion path lemma with the paper's time windows

Source: `fixed_points.tex:1080–1089` and Lemma 5.3 (1106–1137).
The proof transfers the checked independent-copy comparison from threshold
counts to the actual order-statistic windows. Boundary times have zero
exponential measure. No additional probabilistic hypothesis is introduced.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

/-- Probability of the actual open order-statistic window J_j. The arbitrary
zero extension at tied backgrounds is on a proved null set. -/
def ghostOrderKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i j : Fin n) : ℝ≥0∞ :=
  if h : Function.Injective old then
    expMeasure (w.rate i) {t | GhostWindowByOrder old h ell j t}
  else 0

lemma measurableSet_ghostWindowByOrder {n : ℕ} (old : Fin n → ℝ)
    (h : Function.Injective old) (ell : ℕ) (j : Fin n) :
    MeasurableSet {t | GhostWindowByOrder old h ell j t} := by
  unfold GhostWindowByOrder
  split_ifs <;> measurability

/-- Every fixed background has only finitely many boundary times; the
independent exponential insertion avoids all of them almost surely. -/
lemma exponential_avoids_background {n : ℕ} (old : Fin n → ℝ) (r : ℝ) :
    ∀ᵐ t ∂expMeasure r, ∀ i, t ≠ old i := by
  apply ae_all_iff.mpr
  intro i
  exact ae_iff.mpr (by simp)

lemma ghostOrderKernel_eq_count {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old)
    (hnonneg : ∀ i, 0 ≤ old i) (i j : Fin n) :
    ghostOrderKernel w ell old i j = ghostCountKernel w ell old i j := by
  simp only [ghostOrderKernel, hinj, dite_true, ghostCountKernel]
  apply measure_congr
  filter_upwards [exponential_avoids_background old (w.rate i)] with t ht
  exact propext (ghostWindowByOrder_iff_count old hinj hnonneg ell j t ht)

lemma exponentialRace_nonnegative_background {n : ℕ} (w : Weights n) :
    ∀ᵐ old ∂exponentialRace w, ∀ i, 0 ≤ old i := by
  apply ae_all_iff.mpr
  intro i
  apply (mem_ae_iff_prob_eq_one
    (measurableSet_le measurable_const (measurable_pi_apply i))).mpr
  simpa using exponentialRace_survival_ge w i 0 (le_refl 0)

lemma ghostOrderKernel_ae_eq_count {n : ℕ} (w : Weights n) (ell : ℕ) :
    ∀ᵐ old ∂exponentialRace w, ∀ i j,
      ghostOrderKernel w ell old i j = ghostCountKernel w ell old i j := by
  filter_upwards [exponentialRace_injective_ae w,
    exponentialRace_nonnegative_background w] with old hi hn
  exact fun i j => ghostOrderKernel_eq_count w ell old hi hn i j

lemma aemeasurable_ghostOrderKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (i j : Fin n) :
    AEMeasurable (fun old => ghostOrderKernel w ell old i j) (exponentialRace w) :=
  (measurable_ghostCountKernel w ell i j).aemeasurable.congr
    ((ghostOrderKernel_ae_eq_count w ell).mono fun _ h => (h i j).symm)

/-- The kernel is genuinely a probability, including at tied backgrounds. -/
lemma ghostOrderKernel_le_one {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i j : Fin n) : ghostOrderKernel w ell old i j ≤ 1 := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  unfold ghostOrderKernel
  split_ifs
  · exact prob_le_one
  · exact zero_le

/-- Density interpretation of the original kernel. This is the literal
integral defining p_(i,j), rather than a kernel with an assumed bound. -/
theorem ghostOrderKernel_eq_density {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i j : Fin n) :
    ghostOrderKernel w ell old i j =
      ∫⁻ t in {t | GhostWindowByOrder old hinj ell j t},
        exponentialPDF (w.rate i) t := by
  simp only [ghostOrderKernel, hinj, dite_true]
  change (volume.withDensity (exponentialPDF (w.rate i))) _ = _
  exact withDensity_apply _ (measurableSet_ghostWindowByOrder old hinj ell j)

/-- Lemma 5.3 in nonnegative integral form, with explicit K_(ell,m).
It holds for all n and all positive rates, without profile/endpoint/normalization
assumptions. The endpoint v can also be one of the distinct source vertices. -/
theorem finite_insertion_path_ennreal {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    (∫⁻ old,
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, ghostOrderKernel w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
      ∂exponentialRace w) ≤ ((2 * (ell + m + 2) + 1) ^ m : ℕ) := by
  have heq :
      (∫⁻ old,
        ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
          ∏ a, ghostOrderKernel w ell old (u a)
            ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
        ∂exponentialRace w) =
      (∫⁻ old,
        ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
          ∏ a, ghostCountKernel w ell old (u a)
            ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
        ∂exponentialRace w) := by
    apply lintegral_congr_ae
    filter_upwards [ghostOrderKernel_ae_eq_count w ell] with old hold
    simp only [hold]
  rw [heq]
  exact finite_insertion_path_countWindow w ell v

/-- Real-valued p_(i,j) from `eq:ghost-window`. Finiteness follows from its
probability bound, so conversion from ENNReal cannot discard an infinity. -/
def ghostEntry {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (ghostOrderKernel w ell old i j).toReal

/-- The paper's time windows lie in the positive half-line whenever the
background clocks are nonnegative. -/
lemma ghostWindowByOrder_pos {n : ℕ} (old : Fin n → ℝ)
    (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (ell : ℕ) (j : Fin n) {t : ℝ} (ht : GhostWindowByOrder old hinj ell j t) :
    0 < t := by
  have hlow := ht.1
  split_ifs at hlow with hl
  · exact (hnonneg _).trans_lt hlow
  · exact hlow

/-- Exact equality with the original real density integral, together with
its integrability. This closes the representational bridge for p_(i,j). -/
theorem ghostEntry_eq_density_integral {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old)
    (hnonneg : ∀ i, 0 ≤ old i) (i j : Fin n) :
    IntegrableOn (fun t => w.rate i * Real.exp (-(w.rate i * t)))
      {t | GhostWindowByOrder old hinj ell j t} ∧
    ghostEntry w ell old i j =
      ∫ t in {t | GhostWindowByOrder old hinj ell j t},
        w.rate i * Real.exp (-(w.rate i * t)) := by
  let J := {t | GhostWindowByOrder old hinj ell j t}
  have hm : AEMeasurable (exponentialPDF (w.rate i)) (volume.restrict J) :=
    ((measurable_exponentialPDFReal _).ennreal_ofReal).aemeasurable
  have hfinite : (∫⁻ t in J, exponentialPDF (w.rate i) t) ≠ ⊤ := by
    rw [← ghostOrderKernel_eq_density w ell old hinj i j]
    exact ne_of_lt ((ghostOrderKernel_le_one w ell old i j).trans_lt (by simp))
  have heq : (fun t => (exponentialPDF (w.rate i) t).toReal) =ᵐ[volume.restrict J]
      (fun t => w.rate i * Real.exp (-(w.rate i * t))) := by
    filter_upwards [ae_restrict_mem (measurableSet_ghostWindowByOrder old hinj ell j)] with t ht
    rw [exponentialPDF_of_nonneg (ghostWindowByOrder_pos old hinj hnonneg ell j ht).le,
      ENNReal.toReal_ofReal (mul_nonneg (w.positive i).le (Real.exp_pos _).le)]
  refine ⟨(integrable_toReal_of_lintegral_ne_top hm hfinite).congr heq, ?_⟩
  rw [ghostEntry, ghostOrderKernel_eq_density w ell old hinj i j]
  calc
    _ = ∫ t in J, (exponentialPDF (w.rate i) t).toReal := by
      symm
      apply integral_toReal hm
      exact Filter.Eventually.of_forall (fun t => by simp [exponentialPDF])
    _ = _ := integral_congr_ae heq

lemma ghostEntry_mem_Icc {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i j : Fin n) : ghostEntry w ell old i j ∈ Icc (0 : ℝ) 1 := by
  exact ⟨ENNReal.toReal_nonneg,
    (ENNReal.toReal_le_toReal (ne_of_lt ((ghostOrderKernel_le_one w ell old i j).trans_lt
      (by simp))) (by simp)).mpr (ghostOrderKernel_le_one w ell old i j)⟩

/-- Source integrand with the ordered source tuple and final edge exposed. -/
def ghostPathSum {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
    ∏ a, ghostOrderKernel w ell old (u a)
      ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)

lemma aemeasurable_ghostPathSum {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    AEMeasurable (ghostPathSum (m := m) w ell v) (exponentialRace w) := by
  unfold ghostPathSum
  exact Finset.aemeasurable_fun_sum _ (fun u _ =>
    Finset.aemeasurable_fun_prod _ (fun _ _ => aemeasurable_ghostOrderKernel w ell _ _))

lemma ghostPathSum_ne_top {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) : ghostPathSum (m := m) w ell v old ≠ ⊤ := by
  apply ne_of_lt
  apply ENNReal.sum_lt_top.mpr
  intro u _
  apply ENNReal.prod_lt_top
  intro a _
  exact (ghostOrderKernel_le_one w ell old _ _).trans_lt (by simp)

lemma ghostPathSum_toReal {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) :
    (ghostPathSum (m := m) w ell v old).toReal =
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, ghostEntry w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) := by
  unfold ghostPathSum
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_prod, ghostEntry]
  · intro u _
    apply ne_of_lt
    exact ENNReal.prod_lt_top (fun _ _ =>
      (ghostOrderKernel_le_one w ell old _ _).trans_lt (by simp))

/-- Integrability is proved before using the real-valued expectation.
The finite ENNReal estimate prevents a totalized integral from hiding a gap. -/
theorem finite_insertion_path_integrable {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    Integrable (fun old =>
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, ghostEntry w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)) (exponentialRace w) := by
  have hfinite : (∫⁻ old, ghostPathSum (m := m) w ell v old ∂exponentialRace w) ≠ ⊤ :=
    ne_of_lt ((finite_insertion_path_ennreal (m := m) w ell v).trans_lt
      (ENNReal.natCast_lt_top _))
  simpa only [ghostPathSum_toReal] using
    integrable_toReal_of_lintegral_ne_top (aemeasurable_ghostPathSum w ell v) hfinite

/-- Lemma 5.3, exactly as a real expectation of products of the paper's
window probabilities, with K_(ell,m) = (2*(ell+m+2)+1)^m.
The result also includes the harmless empty-path case m=0. -/
theorem finite_insertion_path {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    (∫ old,
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, ghostEntry w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
      ∂exponentialRace w) ≤ ((2 * (ell + m + 2) + 1) ^ m : ℕ) := by
  simp_rw [← ghostPathSum_toReal]
  rw [integral_toReal (aemeasurable_ghostPathSum w ell v)
    (Filter.Eventually.of_forall fun old => lt_top_iff_ne_top.mpr
      (ghostPathSum_ne_top w ell v old))]
  have hfinite : (∫⁻ old, ghostPathSum (m := m) w ell v old ∂exponentialRace w) ≠ ⊤ :=
    ne_of_lt ((finite_insertion_path_ennreal (m := m) w ell v).trans_lt
      (ENNReal.natCast_lt_top _))
  have h := (ENNReal.toReal_le_toReal hfinite (ENNReal.natCast_ne_top _)).mpr
    (finite_insertion_path_ennreal (m := m) w ell v)
  simpa only [ENNReal.toReal_natCast] using h

/-- Integrating the proved window multiplicity gives the row bound
`eq:ghost-row-bound`. The background is fixed throughout the calculation. -/
theorem ghostCountKernel_row_bound {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i : Fin n) :
    ∑ j, ghostCountKernel w ell old i j ≤ ((2 * ell + 1 : ℕ) : ℝ≥0∞) := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  calc
    _ = ∫⁻ t, ((Finset.univ.filter (fun j : Fin n =>
        GhostCountWindow ell old j t)).card : ℝ≥0∞) ∂expMeasure (w.rate i) :=
      sum_measures_eq_lintegral_count _ _ _ (fun j _ =>
        measurableSet_ghostCountWindow ell (fun _ => old) j id
          (fun _ => measurable_const) measurable_id)
    _ ≤ ∫⁻ _t, ((2 * ell + 1 : ℕ) : ℝ≥0∞) ∂expMeasure (w.rate i) := by
      apply lintegral_mono
      intro t
      have hsub : (Finset.univ.filter (fun j : Fin n => GhostCountWindow ell old j t)) ⊆
          Finset.univ.filter (fun j : Fin n =>
            j.val + 1 ≤ clockBeforeCount old t + ell ∧
              clockBeforeCount old t < j.val + 1 + ell) := by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2.2⟩
      dsimp only
      exact_mod_cast (Finset.card_le_card hsub).trans
        (countWindow_multiplicity_le n ell (clockBeforeCount old t))
    _ = _ := by simp

/-- The paper's real row bound for its actual open time windows. Positive
backgrounds in the manuscript satisfy the exposed nonnegativity condition;
that condition also holds almost surely under the actual race law. -/
theorem ghostEntry_row_bound {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ old i) (i : Fin n) :
    ∑ j, ghostEntry w ell old i j ≤ (2 * ell + 1 : ℕ) := by
  by_cases hinj : Function.Injective old
  · have heq : ∀ j, ghostOrderKernel w ell old i j = ghostCountKernel w ell old i j :=
      fun j => ghostOrderKernel_eq_count w ell old hinj hnonneg i j
    have hs : (∑ j, ghostOrderKernel w ell old i j) ≤ ((2 * ell + 1 : ℕ) : ℝ≥0∞) := by
      simpa only [heq] using ghostCountKernel_row_bound w ell old i
    have hfin (j : Fin n) : ghostOrderKernel w ell old i j ≠ ⊤ :=
      ne_of_lt ((ghostOrderKernel_le_one w ell old i j).trans_lt (by simp))
    have h := (ENNReal.toReal_le_toReal
      (ne_of_lt (hs.trans_lt (ENNReal.natCast_lt_top _))) (ENNReal.natCast_ne_top _)).mpr hs
    rw [ENNReal.toReal_sum (fun j _ => hfin j)] at h
    simpa only [ghostEntry, ENNReal.toReal_natCast] using h
  · simp only [ghostEntry, ghostOrderKernel, hinj, dite_false, ENNReal.toReal_zero,
      Finset.sum_const_zero]
    positivity

end Luce
