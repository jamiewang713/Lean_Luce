import Luce.Section6OrderPartition

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
namespace Luce.Section6

theorem deleted_survival_integrable {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n)
    (q : Fin (Finset.univ \ removed).card) (p : ℕ) :
    Integrable (fun old => Real.exp (-((p : ℝ)*w.rate i*
      raceGapStart (compactDeletedClocks removed old) q))) (exponentialRace w) := by
  have hm := (measurable_raceGapStart q).comp (compactDeletedClocks_measurable removed)
  apply (integrable_const (1 : ℝ)).mono'
    (Real.measurable_exp.comp ((hm.const_mul ((p : ℝ)*w.rate i)).neg)).aestronglyMeasurable
  filter_upwards [exponentialRace_injective_ae w, exponentialRace_nonnegative_background w]
    with old hi hn
  have hc := compactDeletedClocks_injective removed old hi
  have hs : 0 ≤ raceGapStart (compactDeletedClocks removed old) q := by
    rw [raceGapStart_eq_consecutiveGapLower _ hc]
    exact consecutiveGapLower_nonneg _ hc (fun k => hn _) q
  change ‖Real.exp (-((p : ℝ)*w.rate i*raceGapStart (compactDeletedClocks removed old) q))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (w.positive i).le) hs))

/-- Sum the order-wise survival contributions into the expectation at the
actual random gap start. All integrability and null-set obligations are proved. -/
theorem deleted_survival_integral_partition {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n)
    (q : Fin (Finset.univ \ removed).card) (p : ℕ) :
    (∫ old, Real.exp (-((p : ℝ)*w.rate i*raceGapStart (compactDeletedClocks removed old) q))
      ∂exponentialRace w) =
    ∑ σ : Equiv.Perm (Fin (Finset.univ \ removed).card),
      ∫ old in {old | StrictMono (fun l => compactDeletedClocks removed old (σ l))},
        Real.exp (-((p : ℝ)*w.rate i*
          previousOrderedTime (fun l => compactDeletedClocks removed old (σ l)) q))
        ∂exponentialRace w := by
  rw [deleted_order_integral_partition w removed _ (deleted_survival_integrable w removed i q p)]
  apply Finset.sum_congr rfl
  intro σ _
  have hS : MeasurableSet {old : Fin n → ℝ |
      StrictMono (fun l => compactDeletedClocks removed old (σ l))} :=
    (measurableSet_strictMono_clocks _).preimage
      (measurable_pi_iff.mpr (fun l => measurable_pi_apply (deletedClockLabel removed (σ l))))
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (exponentialRace_injective_ae w)]
    with old ho hi
  have hc := compactDeletedClocks_injective removed old hi
  have hd : raceDraw (compactDeletedClocks removed old) = σ := by
    rw [raceDraw_eq _ hc]
    exact (drawPermutation_eq_iff_strictMono _ hc σ).mpr ho
  simp only [raceGapStart, hd]

/-- Generic finite-rate helper. The uniform floor is an explicit helper
premise, still to be discharged by the sampled-profile endpoint bounds. -/
theorem deleted_kernel_moment_bound_of_rate_floor {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n)
    (q : Fin (Finset.univ \ removed).card) (p : ℕ) {W : ℝ} (hW : 0 < W)
    (hfloor : ∀ σ, W ≤ orderedRemainingRate (compactDeletedWeights w removed) σ q) :
    (∫ old, (deletedGapKernel w removed old i q.val).toReal^p ∂exponentialRace w) ≤
      (p.factorial : ℝ)*(w.rate i/W)^p*
      (∫ old, Real.exp (-((p : ℝ)*w.rate i*raceGapStart (compactDeletedClocks removed old) q))
        ∂exponentialRace w) := by
  apply (deleted_kernel_moment_sum_bound w removed i q p).trans
  rw [deleted_survival_integral_partition, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_left₀ (div_nonneg (w.positive i).le
        (orderedRemainingRate_pos (compactDeletedWeights w removed) σ q).le)
        (div_le_div_of_nonneg_left (w.positive i).le hW (hfloor σ)) p
    · positivity
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)

end Luce.Section6
