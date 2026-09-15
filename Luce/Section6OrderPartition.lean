import Luce.Section6DeletedOrderMoment

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
namespace Luce.Section6

/-- Sum over every deleted elimination order; tied backgrounds are a proved
null set. This helper's integrability premise is discharged for kernels below. -/
theorem deleted_order_integral_partition {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (F : (Fin n → ℝ) → ℝ)
    (hF : Integrable F (exponentialRace w)) :
    (∫ old, F old ∂exponentialRace w) =
      ∑ σ : Equiv.Perm (Fin (Finset.univ \ removed).card),
        ∫ old in {old | StrictMono (fun l => compactDeletedClocks removed old (σ l))},
          F old ∂exponentialRace w := by
  classical
  letI : MeasurableSpace (Equiv.Perm (Fin (Finset.univ \ removed).card)) := ⊤
  let A := fun σ : Equiv.Perm (Fin (Finset.univ \ removed).card) =>
    {old : Fin n → ℝ | raceDraw (compactDeletedClocks removed old) = σ}
  have hA (σ) : MeasurableSet (A σ) := by
    exact ((measurable_raceDraw _).comp (compactDeletedClocks_measurable removed))
      (t := {σ}) (by trivial)
  have hdis : Pairwise (Disjoint on A) := by
    intro σ τ hne
    apply Set.disjoint_left.mpr
    intro old hs ht
    exact hne (hs.symm.trans ht)
  have hU : (⋃ σ, A σ) = Set.univ := by
    ext old
    simp [A]
  have hi := integral_iUnion_fintype hA hdis (fun _ => hF.integrableOn)
  rw [hU, Measure.restrict_univ] at hi
  rw [hi]
  apply Finset.sum_congr rfl
  intro σ _
  apply setIntegral_congr_set
  filter_upwards [exponentialRace_injective_ae w] with old hold
  apply propext
  have hc := compactDeletedClocks_injective removed old hold
  change raceDraw (compactDeletedClocks removed old) = σ ↔ _
  rw [raceDraw_eq _ hc]
  exact drawPermutation_eq_iff_strictMono _ hc σ

theorem deleted_kernel_power_integrable {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n) (q p : ℕ) :
    Integrable (fun old => (deletedGapKernel w removed old i q).toReal^p) (exponentialRace w) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_deletedGapKernel w removed i q).ennreal_toReal.pow_const p).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro old
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ENNReal.toReal_nonneg p)]
  apply pow_le_one₀ ENNReal.toReal_nonneg
  exact (ENNReal.toReal_le_toReal
    (ne_of_lt ((deletedGapKernel_le_one w removed old i q).trans_lt (by simp))) (by simp)).mpr
    (deletedGapKernel_le_one w removed old i q)

/-- The unconditional insertion moment is bounded by the sum of the exact
order-wise survival contributions, with no extra rate hypotheses. -/
theorem deleted_kernel_moment_sum_bound {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n)
    (q : Fin (Finset.univ \ removed).card) (p : ℕ) :
    (∫ old, (deletedGapKernel w removed old i q.val).toReal^p ∂exponentialRace w) ≤
      ∑ σ : Equiv.Perm (Fin (Finset.univ \ removed).card),
        (p.factorial : ℝ)*(w.rate i/orderedRemainingRate (compactDeletedWeights w removed) σ q)^p*
        (∫ old in {old | StrictMono (fun l => compactDeletedClocks removed old (σ l))},
          Real.exp (-((p : ℝ)*w.rate i*
            previousOrderedTime (fun l => compactDeletedClocks removed old (σ l)) q))
          ∂exponentialRace w) := by
  rw [deleted_order_integral_partition w removed _ (deleted_kernel_power_integrable w removed i q.val p)]
  exact Finset.sum_le_sum (fun σ _ => (deleted_order_kernel_moment_bound w removed i σ q p).2)

end Luce.Section6
