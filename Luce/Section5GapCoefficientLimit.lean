import Luce.Section5MarkedGapBridge
import Luce.Section5Reservoir

/-!
# Uniform convergence of the bounded marked gap coefficient

Source: `fixed_points.tex:1035–1048`. The deterministic reservoir bound is
proved for all eligible deleted times. Bad events are compared as sets;
no measurability of an uncountable supremum is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Luce
attribute [local instance] Classical.propDecidable

/-- Count arrived unmarked labels before applying the reservoir. -/
lemma deletedEmpiricalRemaining_lower_of_reservoir {n r : ℕ} (w : Weights n)
    (hn : 0 < n) (α B : ℝ)
    (hrem : ∀ gone : Finset (Fin n), (gone.card : ℝ) ≤ α * n + r →
      B * n ≤ ∑ i ∈ Finset.univ \ gone, w.rate i)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (t : ℝ)
    (hr : removed.card ≤ r) (ht : deletedEmpiricalArrival removed old t ≤ α) :
    B ≤ deletedEmpiricalRemaining w removed old t := by
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let arrived := (Finset.univ \ removed).filter (fun i => old i ≤ t)
  let gone := removed ∪ arrived
  have hcount : (arrived.card : ℝ) = deletedEmpiricalArrival removed old t * n := by
    rw [deletedEmpiricalArrival, div_mul_cancel₀ _ hN.ne']
    simp only [arrivalAt, Finset.sum_boole, arrived]
  have hgone : (gone.card : ℝ) ≤ α * n + r := by
    have hu : (gone.card : ℝ) ≤ (removed.card : ℝ) + arrived.card := by
      exact_mod_cast Finset.card_union_le removed arrived
    have hr' : (removed.card : ℝ) ≤ r := by exact_mod_cast hr
    have ha := mul_le_mul_of_nonneg_right ht hN.le
    rw [← hcount] at ha
    linarith
  have hset : Finset.univ \ gone =
      (Finset.univ \ removed).filter (fun i => t < old i) := by
    ext i
    simp only [gone, arrived, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_filter, not_or, not_and, not_le]
    tauto
  rw [deletedEmpiricalRemaining, le_div_iff₀ hN]
  have h := hrem gone hgone
  simpa only [hset, Finset.sum_filter] using h

/-- A single positive constant bounds all bulk deleted denominators. -/
theorem ProfileLimit.deleted_remaining_uniform_lower {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop,
      ∀ removed : Finset (Fin n), removed.card ≤ r →
        ∀ old : Fin n → ℝ, ∀ t : ℝ, deletedEmpiricalArrival removed old t ≤ α →
          b ≤ deletedEmpiricalRemaining (w n) removed old t := by
  obtain ⟨d, η, hd, hη, _, hrem⟩ := hf.moderate_reservoir_with_remaining_rate hα
  refine ⟨d * η, mul_pos hd hη, ?_⟩
  filter_upwards [hrem r, eventually_gt_atTop 0] with n hn hn0
  intro removed hr old t ht
  exact deletedEmpiricalRemaining_lower_of_reservoir (w n) hn0 α (d * η) hn removed old t hr ht

/-- The exact scalar error at a deleted time, with its own empirical rank. -/
def deletedGapCoefficientError {n : ℕ} (w : Weights n) (f : ℝ → ℝ)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (t a : ℝ) : ℝ :=
  |rateKernel t a / deletedEmpiricalRemaining w removed old t -
    rateKernel (profileQuantile profileMeasure f (deletedEmpiricalArrival removed old t)) a /
      profileD profileMeasure f (profileQuantile profileMeasure f
        (deletedEmpiricalArrival removed old t))|

/-- The bad event quantifies over every deletion, eligible time and bounded
nonnegative rate; there are no probabilistic hypotheses in this predicate. -/
def DeletedCoefficientBad {n : ℕ} (w : Weights n) (f : ℝ → ℝ)
    (r : ℕ) (α M ε : ℝ) (old : Fin n → ℝ) : Prop :=
  ∃ removed : Finset (Fin n), removed.card ≤ r ∧
    ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed old t ≤ α ∧
      ∃ a ∈ Icc (0 : ℝ) M, ε ≤ deletedGapCoefficientError w f removed old t a

/-- Uniform scalar convergence. The target uses the deleted empirical
rank; the small deterministic shift to the prescribed full rank is separate. -/
theorem section5_uniform_deleted_gap_coefficient
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {old | DeletedCoefficientBad (w n) f r α M ε old}) atTop (𝓝 0) := by
  intro ε hε
  by_cases hα0 : 0 ≤ α
  · obtain ⟨b₀, hb₀, hW⟩ := hf.deleted_remaining_uniform_lower r hα
    let Dα := profileD profileMeasure f (profileQuantile profileMeasure f α)
    obtain ⟨hDα, hD⟩ := section3_denominator_lower hf hα0 hα
    let b := min b₀ Dα
    have hb : 0 < b := lt_min hb₀ hDα
    let C := M ^ 2 / b + M / b ^ 2
    have hC : 0 ≤ C := add_nonneg (div_nonneg (sq_nonneg M) hb.le)
      (div_nonneg hM (sq_nonneg b))
    let δ := ε / (C + 1)
    have hδ : 0 < δ := div_pos hε (by linarith)
    have hCδ : C * δ < ε := by
      have he : (C + 1) * δ = ε := mul_div_cancel₀ ε (by linarith : C + 1 ≠ 0)
      nlinarith
    let Q (n : ℕ) : Set (Fin n → ℝ) :=
      {old | ∃ removed : Finset (Fin n), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed old t ≤ α ∧
          δ ≤ |t - profileQuantile profileMeasure f (deletedEmpiricalArrival removed old t)|}
    let R (n : ℕ) : Set (Fin n → ℝ) :=
      {old | ∃ removed : Finset (Fin n), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed old t ≤ α ∧
          δ ≤ |deletedEmpiricalRemaining (w n) removed old t -
            profileD profileMeasure f (profileQuantile profileMeasure f
              (deletedEmpiricalArrival removed old t))|}
    have hQ := (section5_deleted_order_statistics w f hnorm hf r hα).1 δ hδ
    have hR := section5_deleted_gap_rate w f hnorm hf r hα δ hδ
    have hbound : ∀ᶠ n : ℕ in atTop, exponentialRace (w n)
        {old | DeletedCoefficientBad (w n) f r α M ε old} ≤
        exponentialRace (w n) (Q n) + exponentialRace (w n) (R n) := by
      filter_upwards [hW] with n hn
      refine (measure_mono ?_).trans (measure_union_le (Q n) (R n))
      rintro old ⟨removed, hr, t, ht0, htα, a, ha, hbad⟩
      by_contra hgood
      have hnotQ : old ∉ Q n := fun h => hgood (Or.inl h)
      have hnotR : old ∉ R n := fun h => hgood (Or.inr h)
      have hqt : |t - profileQuantile profileMeasure f (deletedEmpiricalArrival removed old t)| < δ :=
        lt_of_not_ge fun h => hnotQ ⟨removed, hr, t, ht0, htα, h⟩
      have hrt : |deletedEmpiricalRemaining (w n) removed old t -
          profileD profileMeasure f (profileQuantile profileMeasure f
            (deletedEmpiricalArrival removed old t))| < δ :=
        lt_of_not_ge fun h => hnotR ⟨removed, hr, t, ht0, htα, h⟩
      have hx : deletedEmpiricalArrival removed old t ∈ Icc (0 : ℝ) α :=
        ⟨deletedEmpiricalArrival_nonneg removed old t, htα⟩
      have hqt0 := profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hx.1, hx.2.trans_lt hα⟩
      have hbW : b ≤ deletedEmpiricalRemaining (w n) removed old t :=
        (min_le_left b₀ Dα).trans (hn removed hr old t htα)
      have hbD : b ≤ profileD profileMeasure f
          (profileQuantile profileMeasure f (deletedEmpiricalArrival removed old t)) :=
        (min_le_right b₀ Dα).trans (hD _ hx)
      have he := abs_gap_coefficient_sub_le ha.1 ht0 hqt0 hb hbW hbD
      have hcoef : deletedGapCoefficientError (w n) f removed old t a ≤ C * δ := by
        apply he.trans
        dsimp [C]
        rw [add_mul]
        gcongr
        · exact ha.1
        · exact ha.2
        · exact ha.2
      exact (not_le_of_gt (hcoef.trans_lt hCδ)) hbad
    have hlim := hQ.add hR
    simp only [add_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) hbound
  · have hempty (n : ℕ) : {old | DeletedCoefficientBad (w n) f r α M ε old} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro old ⟨removed, _, t, _, htα, _⟩
      exact hα0 ((deletedEmpiricalArrival_nonneg removed old t).trans htα)
    simp_rw [hempty, measure_empty]
    exact tendsto_const_nhds

end Luce
