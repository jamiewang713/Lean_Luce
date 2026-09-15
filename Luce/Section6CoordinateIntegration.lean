import Luce.ExponentialFacts
import Mathlib.MeasureTheory.Integral.Marginal

/-! Generic product-measure tools for the single-coordinate proof of Lemma 6.6.
All marginal laws here are arbitrary probability measures on the real line. -/

noncomputable section
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- Inserting a fresh value with the original marginal law preserves the
integral. The unused old coordinate is integrated against a probability law. -/
theorem lintegral_single_coordinate {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n)
    (f : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂Measure.pi μ) =
      ∫⁻ t, ∫⁻ x, f (update x i t) ∂Measure.pi μ ∂μ i := by
  let g : (Fin n → ℝ) → ℝ≥0∞ := fun x => ∫⁻ t, f (update x i t) ∂μ i
  have hg : Measurable g := by
    simpa only [lmarginal_singleton] using hf.lmarginal μ (s := {i})
  have he : (∫⁻ x, f x ∂Measure.pi μ) = ∫⁻ x, g x ∂Measure.pi μ := by
    apply lintegral_eq_of_lmarginal_eq {i} hf hg
    rw [lmarginal_singleton, lmarginal_singleton]
    funext x
    simp only [g, update_idem]
    simp
  rw [he]
  exact lintegral_lintegral_swap (hf.comp measurable_update').aemeasurable

/-- Common-background bound after replacing one marginal by a dominating
measure. Tonelli is applied only to nonnegative measurable functions. -/
theorem single_coordinate_sum_bound {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (ν : Measure ℝ) [SFinite ν]
    (S : Finset (Fin n)) (f : Fin n → (Fin n → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hdom : ∀ i ∈ S, μ i ≤ ν)
    (C : ℝ≥0∞)
    (hcount : ∀ t, ∀ᵐ x ∂Measure.pi μ, ∑ i ∈ S, f i (update x i t) ≤ C) :
    (∫⁻ x, ∑ i ∈ S, f i x ∂Measure.pi μ) ≤ C * ν univ := by
  have hm (i : Fin n) : Measurable (fun t => ∫⁻ x, f i (update x i t) ∂Measure.pi μ) := by
    have hmi : Measurable (fun z : ℝ × (Fin n → ℝ) => f i (update z.2 i z.1)) :=
      (hf i).comp (measurable_update'.comp measurable_swap)
    exact hmi.lintegral_prod_right
  calc
    _ = ∑ i ∈ S, ∫⁻ x, f i x ∂Measure.pi μ :=
      lintegral_finsetSum S (fun i _ => hf i)
    _ = ∑ i ∈ S, ∫⁻ t, ∫⁻ x, f i (update x i t) ∂Measure.pi μ ∂μ i := by
      apply Finset.sum_congr rfl
      intro i _
      exact lintegral_single_coordinate μ i (f i) (hf i)
    _ ≤ ∑ i ∈ S, ∫⁻ t, ∫⁻ x, f i (update x i t) ∂Measure.pi μ ∂ν := by
      apply Finset.sum_le_sum
      intro i hi
      exact lintegral_mono' (hdom i hi) (fun _ => le_rfl)
    _ = ∫⁻ t, ∑ i ∈ S, ∫⁻ x, f i (update x i t) ∂Measure.pi μ ∂ν :=
      (lintegral_finsetSum S (fun i _ => hm i)).symm
    _ = ∫⁻ t, ∫⁻ x, ∑ i ∈ S, f i (update x i t) ∂Measure.pi μ ∂ν := by
      apply lintegral_congr
      intro t
      exact (lintegral_finsetSum S (fun i _ =>
        (hf i).comp measurable_update_left)).symm
    _ ≤ ∫⁻ _t, C ∂ν := by
      apply lintegral_mono
      intro t
      simpa using (lintegral_mono_ae (hcount t))
    _ = _ := lintegral_const C

theorem independent_real_coordinates_injective_ae {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] :
    ∀ᵐ x ∂Measure.pi μ, Injective x := by
  have hpair (i j : Fin n) (hij : i ≠ j) :
      (Measure.pi μ) {x | x i = x j} = 0 := by
    have h := (iIndepFun_pi (μ := μ) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hij
    have hm := h.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable
    rw [(measurePreserving_eval μ i).map_eq, (measurePreserving_eval μ j).map_eq] at hm
    have he : {x : Fin n → ℝ | x i = x j} =
        (fun x => (x i, x j)) ⁻¹' Set.diagonal ℝ := rfl
    rw [he, ← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      measurableSet_diagonal, hm, Measure.prod_apply measurableSet_diagonal]
    simp [Set.diagonal]
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ => hij
  · have hn : ∀ᵐ x ∂Measure.pi μ, x i ≠ x j := by
      rw [ae_iff]
      simpa only [not_not] using hpair i j hij
    exact hn.mono fun _ hne he => (hne he).elim

theorem independent_real_coordinates_avoid_ae {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (t : ℝ) :
    ∀ᵐ x ∂Measure.pi μ, ∀ j, t ≠ x j := by
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval μ j).quasiMeasurePreserving.ae
    ((μ j).ae_ne t |>.mono fun _ h => h.symm)

end Luce.Section6
