import Luce.Section5FiniteInsertion

/-!
# The ghost cylinder bound

This file proves `fixed_points.tex:1090–1095`, equation
`eq:ghost-cylinder-bound`, using the actual independent exponential law.
Only the marked labels are replaced. Their distinctness is used to identify
the conditional probability with a product; target ranks may be arbitrary.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

/-- A new clock is not before itself. Thus the upper change in its
before-count uses at most the other replaced labels. This sharp one-rank
saving is necessary for the lower endpoint of the paper's open window. -/
theorem clockBeforeCount_le_add_erase_self_of_eq_off {n : ℕ}
    (old new : Fin n → ℝ) (s : Finset (Fin n))
    (hsame : ∀ k, k ∉ s → new k = old k) (i : Fin n) :
    clockBeforeCount new (new i) ≤ clockBeforeCount old (new i) + (s.erase i).card := by
  have hsub : (Finset.univ.filter fun k => new k < new i) ⊆
      (Finset.univ.filter fun k => old k < new i) ∪ s.erase i := by
    intro k hk
    have hkt := (Finset.mem_filter.mp hk).2
    by_cases hks : k ∈ s
    · apply Finset.mem_union_right
      apply Finset.mem_erase.mpr
      refine ⟨?_, hks⟩
      intro he
      subst k
      exact (lt_irrefl _ hkt)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [← hsame k hks]⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- The exact rank cylinder in the source, retaining its one-based ranks. -/
def MarkedRankCylinder {n ell : ℕ} (u j : Fin ell → Fin n)
    (clocks : Fin n → ℝ) : Prop :=
  ∀ a, raceRank clocks (u a) = (j a).val + 1

/-- Simultaneous success of the independent replacement clocks in their
prescribed rank windows, all relative to one background. -/
def GhostMarkedSuccess {n ell : ℕ} (u j : Fin ell → Fin n)
    (c : Fin n → ℝ × ℝ) : Prop :=
  ∀ a, GhostCountWindow ell (fun i => (c i).1) (j a) (c (u a)).2

lemma measurableSet_markedRankCylinder {n ell : ℕ} (u j : Fin ell → Fin n) :
    MeasurableSet {clocks | MarkedRankCylinder u j clocks} := by
  simp only [MarkedRankCylinder, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  have hm := measurable_clockBeforeCount (fun c : Fin n → ℝ => c)
    (fun c => c (u a)) (fun i => measurable_pi_apply i) (measurable_pi_apply (u a))
  exact measurableSet_eq_fun (hm.const_add 1) measurable_const

lemma measurableSet_ghostMarkedSuccess {n ell : ℕ} (u j : Fin ell → Fin n) :
    MeasurableSet {c | GhostMarkedSuccess u j c} := by
  simp only [GhostMarkedSuccess, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply measurableSet_ghostCountWindow
  · intro i; exact measurable_fst.comp (measurable_pi_apply i)
  · exact measurable_snd.comp (measurable_pi_apply (u a))

/-- Every prescribed new rank lies in the corresponding old ghost window.
The lower bound counts at most `ell-1` changed competitors; the upper bound
counts at most `ell`. No bound is assumed on the rates or spacings. -/
theorem swapped_rankCylinder_implies_ghost {n ell : ℕ}
    (u j : Fin ell → Fin n) (c : Fin n → ℝ × ℝ)
    (hpos : ∀ i, 0 < (swapClockCopies (Finset.univ.image u) c i).1)
    (hrank : MarkedRankCylinder u j
      (fun i => (swapClockCopies (Finset.univ.image u) c i).1)) :
    GhostMarkedSuccess u j c := by
  intro a
  let s := Finset.univ.image u
  let old := fun i => (c i).1
  let new := fun i => (swapClockCopies s c i).1
  have hi : u a ∈ s := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hsame : ∀ i, i ∉ s → new i = old i := by
    intro i hi
    simp [new, old, swapClockCopies, hi]
  have hnew : new (u a) = (c (u a)).2 := by simp [new, swapClockCopies, hi]
  have hcard : s.card ≤ ell := by
    simpa [s] using (Finset.card_image_le (s := Finset.univ) (f := u))
  have herase := Finset.card_erase_add_one hi
  have hlow := clockBeforeCount_le_add_erase_self_of_eq_off old new s hsame (u a)
  have hupp := clockBeforeCount_le_add_of_eq_off new old s
    (fun i hi => (hsame i hi).symm) (new (u a))
  have hr := hrank a
  change 1 + clockBeforeCount new (new (u a)) = (j a).val + 1 at hr
  change 0 < (c (u a)).2 ∧ (j a).val + 1 ≤ clockBeforeCount old (c (u a)).2 + ell ∧
    clockBeforeCount old (c (u a)).2 < (j a).val + 1 + ell
  rw [← hnew]
  exact ⟨hpos (u a), by omega, by omega⟩

lemma exponentialRace_positive_background {n : ℕ} (w : Weights n) :
    ∀ᵐ clocks ∂exponentialRace w, ∀ i, 0 < clocks i := by
  apply ae_all_iff.mpr
  intro i
  apply (mem_ae_iff_prob_eq_one
    (measurableSet_lt measurable_const (measurable_pi_apply i))).mpr
  simpa using exponentialRace_survival w i 0 (le_refl 0)

/-- Resampling the marked labels preserves the race law, and every
successful cylinder is contained in the ghost-window event. -/
theorem markedRankCylinder_probability_le_ghost {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} ≤
      pairedExponentialRace w {c | GhostMarkedSuccess u j c} := by
  calc
    _ = pairedExponentialRace w {c | MarkedRankCylinder u j
        (fun i => (swapClockCopies (Finset.univ.image u) c i).1)} :=
      ((swapped_background_measurePreserving w (Finset.univ.image u)).measure_preimage
        (measurableSet_markedRankCylinder u j).nullMeasurableSet).symm
    _ ≤ _ := by
      apply measure_mono_ae
      filter_upwards [(swapped_background_measurePreserving w (Finset.univ.image u)).quasiMeasurePreserving.ae
        (exponentialRace_positive_background w)] with c hc
      exact fun hr => swapped_rankCylinder_implies_ghost u j c hc hr

/-- Conditional independence for arbitrary prescribed targets. Distinctness
is a condition on the sources only, as in the paper's cylinder probability. -/
theorem ghostCountKernel_marked_product {n ell : ℕ} (w : Weights n)
    (old : Fin n → ℝ) (u j : Fin ell → Fin n) (hu : Function.Injective u) :
    exponentialRace w {new | ∀ a, GhostCountWindow ell old (j a) (new (u a))} =
      ∏ a, ghostCountKernel w ell old (u a) (j a) := by
  let sets := fun a : Fin ell => {t | GhostCountWindow ell old (j a) t}
  have hs : ∀ a, MeasurableSet (sets a) := by
    intro a
    exact measurableSet_ghostCountWindow ell (fun _ => old) _ id
      (fun _ => measurable_const) measurable_id
  have h := ((exponentialRace_independent w).precomp hu).measure_inter_preimage_eq_mul
    Finset.univ (sets := sets) (fun a _ => hs a)
  simp only [Finset.mem_univ, iInter_true] at h
  have heq : (⋂ a, (fun new : Fin n → ℝ => new (u a)) ⁻¹' sets a) =
      {new | ∀ a, GhostCountWindow ell old (j a) (new (u a))} := by
    ext new
    simp [sets]
  rw [← heq, h]
  apply Finset.prod_congr rfl
  intro a _
  exact (exponentialRace_eval w (u a)).measure_preimage (hs a).nullMeasurableSet

/-- Tonelli turns the conditional product into the probability of joint
success of the replacement clocks. -/
theorem lintegral_ghostCountKernel_marked_product {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) (hu : Function.Injective u) :
    (∫⁻ old, ∏ a, ghostCountKernel w ell old (u a) (j a) ∂exponentialRace w) =
      pairedExponentialRace w {c | GhostMarkedSuccess u j c} := by
  let A := {c : (Fin n → ℝ) × (Fin n → ℝ) |
    ∀ a, GhostCountWindow ell c.1 (j a) (c.2 (u a))}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    apply measurableSet_ghostCountWindow
    · intro i; exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply (u a)).comp measurable_snd
  calc
    _ = ∫⁻ old, exponentialRace w ((Prod.mk old) ⁻¹' A) ∂exponentialRace w := by
      apply lintegral_congr
      intro old
      exact (ghostCountKernel_marked_product w old u j hu).symm
    _ = ((exponentialRace w).prod (exponentialRace w)) A := (Measure.prod_apply hA).symm
    _ = pairedExponentialRace w
        ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) ⁻¹' A) :=
      ((pairedExponentialRace_families w).measure_preimage hA.nullMeasurableSet).symm
    _ = _ := rfl

/-- Equation `eq:ghost-cylinder-bound` with the paper's actual time-window
probabilities, in nonnegative integral form. -/
theorem ghost_cylinder_bound_ennreal {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) (hu : Function.Injective u) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} ≤
      ∫⁻ old, ∏ a, ghostOrderKernel w ell old (u a) (j a) ∂exponentialRace w := by
  calc
    _ ≤ pairedExponentialRace w {c | GhostMarkedSuccess u j c} :=
      markedRankCylinder_probability_le_ghost w u j
    _ = ∫⁻ old, ∏ a, ghostCountKernel w ell old (u a) (j a) ∂exponentialRace w :=
      (lintegral_ghostCountKernel_marked_product w u j hu).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ghostOrderKernel_ae_eq_count w ell] with old hold
      simp only [hold]

/-- The cylinder product is measurable almost everywhere and is bounded
by one; no infinite or undefined real expectation is used. -/
lemma aemeasurable_ghostCylinderProduct {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) :
    AEMeasurable (fun old => ∏ a, ghostOrderKernel w ell old (u a) (j a))
      (exponentialRace w) :=
  Finset.aemeasurable_fun_prod _ (fun _ _ => aemeasurable_ghostOrderKernel w ell _ _)

lemma ghostCylinderProduct_le_one {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) (old : Fin n → ℝ) :
    (∏ a, ghostOrderKernel w ell old (u a) (j a)) ≤ 1 :=
  Finset.prod_le_one (fun _ _ => zero_le) (fun _ _ => ghostOrderKernel_le_one w ell old _ _)

lemma lintegral_ghostCylinderProduct_le_one {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) :
    (∫⁻ old, ∏ a, ghostOrderKernel w ell old (u a) (j a) ∂exponentialRace w) ≤ 1 := by
  calc
    _ ≤ ∫⁻ _old : Fin n → ℝ, (1 : ℝ≥0∞) ∂exponentialRace w :=
      lintegral_mono (ghostCylinderProduct_le_one w u j)
    _ = _ := by simp

theorem ghost_cylinder_product_integrable {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) :
    Integrable (fun old => ∏ a, ghostEntry w ell old (u a) (j a))
      (exponentialRace w) := by
  have hfinite : (∫⁻ old, ∏ a, ghostOrderKernel w ell old (u a) (j a)
      ∂exponentialRace w) ≠ ⊤ :=
    ne_of_lt ((lintegral_ghostCylinderProduct_le_one w u j).trans_lt (by simp))
  simpa only [ENNReal.toReal_prod, ghostEntry] using
    integrable_toReal_of_lintegral_ne_top (aemeasurable_ghostCylinderProduct w u j) hfinite

/-- Equation `eq:ghost-cylinder-bound`, as the real probability and real
expectation stated in the manuscript. The `ell` sources are distinct; no
restriction on the prescribed target ranks has been added. -/
theorem ghost_cylinder_bound {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) (hu : Function.Injective u) :
    (exponentialRace w).real {clocks | ∀ a, raceRank clocks (u a) = (j a).val + 1} ≤
      ∫ old, ∏ a, ghostEntry w ell old (u a) (j a) ∂exponentialRace w := by
  have hfinite : (∫⁻ old, ∏ a, ghostOrderKernel w ell old (u a) (j a)
      ∂exponentialRace w) ≠ ⊤ :=
    ne_of_lt ((lintegral_ghostCylinderProduct_le_one w u j).trans_lt (by simp))
  have h := (ENNReal.toReal_le_toReal (measure_ne_top _ _) hfinite).mpr
    (ghost_cylinder_bound_ennreal w u j hu)
  have hi := integral_toReal (aemeasurable_ghostCylinderProduct w u j)
    (Filter.Eventually.of_forall fun old =>
      (ghostCylinderProduct_le_one w u j old).trans_lt (by simp))
  rw [← hi] at h
  simpa only [measureReal_def, MarkedRankCylinder, ENNReal.toReal_prod, ghostEntry] using h

end Luce
