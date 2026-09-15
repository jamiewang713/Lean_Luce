import Luce.Section5GhostTimeSplit

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Luce

/-- Density representation for any measurable part of the literal ghost window. -/
theorem ghost_subwindow_density {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (i v : Fin n) (T : Set ℝ) (hT : MeasurableSet T)
    (hsub : T ⊆ {t | GhostWindowByOrder old hinj ell v t}) :
    (expMeasure (w.rate i)).real T =
      ∫ t in T, w.rate i * Real.exp (-w.rate i * t) := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  have hkernel : expMeasure (w.rate i) T = ∫⁻ t in T, exponentialPDF (w.rate i) t :=
    withDensity_apply _ hT
  have hm : AEMeasurable (exponentialPDF (w.rate i)) (volume.restrict T) :=
    (measurable_exponentialPDFReal _).ennreal_ofReal.aemeasurable
  have heq : (fun t => (exponentialPDF (w.rate i) t).toReal) =ᵐ[volume.restrict T]
      (fun t => w.rate i * Real.exp (-w.rate i * t)) := by
    filter_upwards [ae_restrict_mem hT] with t ht
    rw [exponentialPDF_of_nonneg (ghostWindowByOrder_pos old hinj hnonneg ell v (hsub ht)).le,
      ENNReal.toReal_ofReal (mul_nonneg (w.positive i).le (Real.exp_pos _).le)]
    simp only [neg_mul]
  rw [Measure.real, hkernel]
  calc
    _ = ∫ t in T, (exponentialPDF (w.rate i) t).toReal := by
      symm
      exact integral_toReal hm (Filter.Eventually.of_forall fun t => by simp [exponentialPDF])
    _ = _ := integral_congr_ae heq

theorem lateGhostEntry_eq_window_integral {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (i v : Fin n) (s : ℝ) :
    lateGhostEntry w ell old hinj i v s =
      ∫ t in Set.Ioi s, {t | GhostWindowByOrder old hinj ell v t}.indicator
        (fun t => w.rate i * Real.exp (-w.rate i*t)) t := by
  rw [integral_indicator (measurableSet_ghostWindowByOrder old hinj ell v),
    Measure.restrict_restrict (measurableSet_ghostWindowByOrder old hinj ell v)]
  have hset : {t | GhostWindowByOrder old hinj ell v t} \ Set.Iic s =
      {t | GhostWindowByOrder old hinj ell v t} ∩ Set.Ioi s := by
    ext t
    simp
  unfold lateGhostEntry
  rw [hset]
  exact ghost_subwindow_density w ell old hinj hnonneg i v _
    ((measurableSet_ghostWindowByOrder old hinj ell v).inter measurableSet_Ioi)
    Set.inter_subset_left

theorem lateGhostEntry_antitone {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i v : Fin n) :
    Antitone (lateGhostEntry w ell old hinj i v) := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  intro s t hst
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro x hx
  exact ⟨hx.1, fun hxs => hx.2 (hxs.trans hst)⟩

end Luce
