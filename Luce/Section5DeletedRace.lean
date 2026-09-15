import Luce.Section3OrderStats

/-!
# Uniform empirical race estimates after finitely many deletions

Source: `fixed_points.tex:1035–1038`. The deleted clocks may depend on the
row and are controlled simultaneously. Their arrival contribution is at most
`r/n`; their rate contribution is at most `r` times the largest normalized
weight, which tends to zero by the actual profile assumption. These are
macroscopic estimates, not a claim of a microscopic gap law.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- The unmarked empirical arrival count, normalized by the original row
size `n`, as in the deleted-chain proof in Section 5. -/
def deletedEmpiricalArrival {n : ℕ} (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ removed, arrivalAt t (clocks i)) / n

/-- The unmarked weak-survival rate, again divided by the original `n`. -/
def deletedEmpiricalRemainingGe {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ removed, if t ≤ clocks i then w.rate i else 0) / n

lemma deletedEmpiricalArrival_nonneg {n : ℕ} (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) : 0 ≤ deletedEmpiricalArrival removed clocks t := by
  exact div_nonneg (Finset.sum_nonneg fun i _ => (arrivalAt_mem_Icc t (clocks i)).1)
    (Nat.cast_nonneg n)

lemma deletedEmpiricalArrival_monotone {n : ℕ} (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) : Monotone (deletedEmpiricalArrival removed clocks) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact Finset.sum_le_sum fun i _ => arrivalAt_monotone (clocks i) hst

/-- Exact finite-sum accounting, before any probabilistic estimate. -/
lemma empiricalArrival_sub_deleted {n : ℕ} (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) :
    empiricalArrival clocks t - deletedEmpiricalArrival removed clocks t =
      (∑ i ∈ removed, arrivalAt t (clocks i)) / n := by
  have h := Finset.sum_sdiff (Finset.subset_univ removed)
    (f := fun i => arrivalAt t (clocks i))
  unfold empiricalArrival deletedEmpiricalArrival
  rw [← h]
  ring

/-- Deleting `r` clocks changes the empirical arrival count by at most `r/n`,
uniformly over times, clock configurations, and the removed labels. -/
lemma deletedEmpiricalArrival_error {n r : ℕ} (removed : Finset (Fin n))
    (hr : removed.card ≤ r) (clocks : Fin n → ℝ) (t : ℝ) :
    |deletedEmpiricalArrival removed clocks t - empiricalArrival clocks t| ≤ (r : ℝ) / n := by
  rw [abs_sub_comm, empiricalArrival_sub_deleted,
    abs_of_nonneg (div_nonneg (Finset.sum_nonneg fun i _ =>
      (arrivalAt_mem_Icc t (clocks i)).1) (Nat.cast_nonneg n))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    _ ≤ ∑ _i ∈ removed, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => (arrivalAt_mem_Icc t (clocks i)).2
    _ = (removed.card : ℝ) := by simp
    _ ≤ r := by exact_mod_cast hr

/-- Exact finite-sum accounting for the unmarked remaining rate. -/
lemma empiricalRemainingGe_sub_deleted {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (clocks : Fin n → ℝ) (t : ℝ) :
    empiricalRemainingGe w clocks t - deletedEmpiricalRemainingGe w removed clocks t =
      (∑ i ∈ removed, if t ≤ clocks i then w.rate i else 0) / n := by
  have h := Finset.sum_sdiff (Finset.subset_univ removed)
    (f := fun i => if t ≤ clocks i then w.rate i else 0)
  unfold empiricalRemainingGe deletedEmpiricalRemainingGe
  rw [← h]
  ring

/-- The source's uniform deletion error. Bounded marked rates are unnecessary:
the largest normalized weight is already negligible under Assumption 1.1. -/
lemma deletedEmpiricalRemainingGe_error (w : WeightArray) {n r : ℕ}
    (removed : Finset (Fin (n + 1))) (hr : removed.card ≤ r)
    (clocks : Fin (n + 1) → ℝ) (t : ℝ) :
    |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t -
      empiricalRemainingGe (w (n + 1)) clocks t| ≤
        (r : ℝ) * (rowMaxRate w n / (n + 1 : ℕ)) := by
  have hterm (i : Fin (n + 1)) :
      0 ≤ (if t ≤ clocks i then (w (n + 1)).rate i else 0) := by
    split_ifs
    · exact (w (n + 1)).positive i |>.le
    · exact le_rfl
  have hmax : 0 ≤ rowMaxRate w n :=
    ((w (n + 1)).positive 0).le.trans (rate_le_rowMaxRate w n 0)
  rw [abs_sub_comm, empiricalRemainingGe_sub_deleted,
    abs_of_nonneg (div_nonneg (Finset.sum_nonneg fun i _ => hterm i) (by positivity))]
  calc
    _ ≤ ((removed.card : ℝ) * rowMaxRate w n) / (n + 1 : ℕ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ ∑ _i ∈ removed, rowMaxRate w n := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs
          · exact rate_le_rowMaxRate w n i
          · exact hmax
        _ = _ := by simp
    _ ≤ ((r : ℝ) * rowMaxRate w n) / (n + 1 : ℕ) := by
      gcongr
    _ = _ := by ring

/-- The deleted empirical CDF converges uniformly on compact time intervals,
simultaneously over all sets of at most `r` deleted clocks (source 1035–1038). -/
theorem section5_uniform_deleted_arrival
    (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f) (r : ℕ) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t ∈ Icc 0 T, ε ≤ |deletedEmpiricalArrival removed clocks t -
          profileF profileMeasure f t|}) atTop (𝓝 0) := by
  intro ε hε
  have herr : Tendsto (fun n : ℕ => (r : ℝ) / (n + 1 : ℕ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r : ℝ)
  have he : ∀ᶠ n : ℕ in atTop, (r : ℝ) / (n + 1 : ℕ) < ε / 2 :=
    herr.eventually (gt_mem_nhds (half_pos hε))
  have hbound : ∀ᶠ n : ℕ in atTop, exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t ∈ Icc 0 T, ε ≤ |deletedEmpiricalArrival removed clocks t -
          profileF profileMeasure f t|} ≤
      exponentialRace (w (n + 1))
        {clocks | ∃ t ∈ Icc 0 T, ε / 2 ≤ |empiricalArrival clocks t -
          profileF profileMeasure f t|} := by
    filter_upwards [he] with n hn
    apply measure_mono
    rintro clocks ⟨removed, hr, t, ht, hbad⟩
    refine ⟨t, ht, ?_⟩
    have hdel := deletedEmpiricalArrival_error removed hr clocks t
    have htri := abs_sub_le (deletedEmpiricalArrival removed clocks t)
      (empiricalArrival clocks t) (profileF profileMeasure f t)
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (section3_uniform_arrival w f hf T (ε / 2) (half_pos hε))
    (Eventually.of_forall fun _ => bot_le) hbound

/-- The corresponding deleted remaining-rate convergence, with normalization
exposed exactly as in the source's full race estimate. -/
theorem section5_uniform_deleted_remaining
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t ∈ Icc 0 T, ε ≤ |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t -
          profileD profileMeasure f t|}) atTop (𝓝 0) := by
  intro ε hε
  have herr : Tendsto (fun n => (r : ℝ) * (rowMaxRate w n / (n + 1 : ℕ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hf.max_weight_div_tendsto_zero.const_mul (r : ℝ)
  have he : ∀ᶠ n : ℕ in atTop, (r : ℝ) * (rowMaxRate w n / (n + 1 : ℕ)) < ε / 2 :=
    herr.eventually (gt_mem_nhds (half_pos hε))
  have hbound : ∀ᶠ n : ℕ in atTop, exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t ∈ Icc 0 T, ε ≤ |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t -
          profileD profileMeasure f t|} ≤
      exponentialRace (w (n + 1))
        {clocks | ∃ t ∈ Icc 0 T, ε / 2 ≤ |empiricalRemainingGe (w (n + 1)) clocks t -
          profileD profileMeasure f t|} := by
    filter_upwards [he] with n hn
    apply measure_mono
    rintro clocks ⟨removed, hr, t, ht, hbad⟩
    refine ⟨t, ht, ?_⟩
    have hdel := deletedEmpiricalRemainingGe_error w removed hr clocks t
    have htri := abs_sub_le (deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t)
      (empiricalRemainingGe (w (n + 1)) clocks t) (profileD profileMeasure f t)
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (section3_uniform_remaining w f hnorm hf T (ε / 2) (half_pos hε))
    (Eventually.of_forall fun _ => bot_le) hbound

/-- The empirical coordinate is the exact number of arrived unmarked
clocks divided by `n`, retaining both the global normalization and labels. -/
lemma deletedEmpiricalArrival_eq_count {n : ℕ} (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) :
    deletedEmpiricalArrival removed clocks t =
      (((Finset.univ \ removed).filter (fun i => clocks i ≤ t)).card : ℝ) / n := by
  simp only [deletedEmpiricalArrival, arrivalAt, Finset.sum_boole]

/-- Uniform inverse-time control for the actual deleted process. Evaluating
this at its successive arrival times gives the unmarked order-statistic
estimate used at source 1035–1038. The theorem is stronger: it controls every
nonnegative time whose unmarked empirical rank lies in the bulk, including
the entire intervening gaps. -/
theorem section5_uniform_deleted_quantile
    (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f) (r : ℕ)
    {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |t - profileQuantile profileMeasure f
            (deletedEmpiricalArrival removed clocks t)|}) atTop (𝓝 0) := by
  intro ε hε
  by_cases hα0 : 0 ≤ α
  · obtain ⟨T, δ, hT, hδ, hmargin, hinv⟩ :=
      uniform_profile_inverse_modulus hf.integrable hf.ae_pos hα0 hα hε
    have hbound (n : ℕ) : exponentialRace (w (n + 1))
        {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
          ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
            ε ≤ |t - profileQuantile profileMeasure f
              (deletedEmpiricalArrival removed clocks t)|} ≤
        exponentialRace (w (n + 1))
          {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
            ∃ t ∈ Icc 0 T, δ ≤ |deletedEmpiricalArrival removed clocks t -
              profileF profileMeasure f t|} := by
      apply measure_mono
      rintro clocks ⟨removed, hr, t, ht0, htα, hbad⟩
      by_contra hnot
      have hgood : ∀ s ∈ Icc (0 : ℝ) T,
          |deletedEmpiricalArrival removed clocks s - profileF profileMeasure f s| < δ := by
        intro s hs
        exact lt_of_not_ge fun h => hnot ⟨removed, hr, s, hs, h⟩
      have hGT : α < deletedEmpiricalArrival removed clocks T := by
        have h := (abs_lt.mp (hgood T ⟨hT, le_rfl⟩)).1
        linarith
      have htT : t ≤ T := by
        by_contra h
        have hmono := deletedEmpiricalArrival_monotone removed clocks (le_of_not_ge h)
        exact (not_le_of_gt hGT) (hmono.trans htα)
      have herror := hgood t ⟨ht0, htT⟩
      rw [abs_sub_comm] at herror
      exact (not_lt_of_ge hbad) (hinv (deletedEmpiricalArrival removed clocks t)
        ⟨deletedEmpiricalArrival_nonneg removed clocks t, htα⟩ t ⟨ht0, htT⟩ herror)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (section5_uniform_deleted_arrival w f hf r T δ hδ) (fun _ => bot_le) hbound
  · have hempty (n : ℕ) :
        {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
          ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
            ε ≤ |t - profileQuantile profileMeasure f
              (deletedEmpiricalArrival removed clocks t)|} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro clocks ⟨removed, _, t, _, htα, _⟩
      exact hα0 ((deletedEmpiricalArrival_nonneg removed clocks t).trans htα)
    simp_rw [hempty, measure_empty]
    exact tendsto_const_nhds

/-- The unmarked remaining rate at every bulk time has the deterministic
value at its unmarked quantile, uniformly over all permitted deletions.
This proves the random-time substitution needed before studying gap moments. -/
theorem section5_uniform_deleted_denominator
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t -
            profileD profileMeasure f (profileQuantile profileMeasure f
              (deletedEmpiricalArrival removed clocks t))|}) atTop (𝓝 0) := by
  intro ε hε
  by_cases hα0 : 0 ≤ α
  · let q := profileQuantile profileMeasure f
    let D := profileD profileMeasure f
    let T := q α + 1
    have hqα : 0 ≤ q α := profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hα0, hα⟩
    have hT : 0 ≤ T := by dsimp [T]; linarith
    have hc : ContinuousOn D (Icc 0 T) :=
      (continuousOn_profileD hf.integrable hf.ae_nonneg).mono (fun _ ht => ht.1)
    obtain ⟨a, ha, hmod⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hc) (ε / 2) (half_pos hε)
    let δ := min a 1
    have hδ : 0 < δ := lt_min ha zero_lt_one
    let Q (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          δ ≤ |t - q (deletedEmpiricalArrival removed clocks t)|}
    let R (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t ∈ Icc 0 T, ε / 2 ≤ |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t - D t|}
    have hQ : Tendsto (fun n => exponentialRace (w (n + 1)) (Q n)) atTop (𝓝 0) :=
      section5_uniform_deleted_quantile w f hf r hα δ hδ
    have hR : Tendsto (fun n => exponentialRace (w (n + 1)) (R n)) atTop (𝓝 0) :=
      section5_uniform_deleted_remaining w f hnorm hf r T (ε / 2) (half_pos hε)
    have hbound (n : ℕ) : exponentialRace (w (n + 1))
        {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
          ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
            ε ≤ |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t -
              D (q (deletedEmpiricalArrival removed clocks t))|} ≤
        exponentialRace (w (n + 1)) (R n) + exponentialRace (w (n + 1)) (Q n) := by
      refine (measure_mono ?_).trans (measure_union_le (R n) (Q n))
      rintro clocks ⟨removed, hr, t, ht0, htα, hbad⟩
      by_contra hgood
      have hnotR : clocks ∉ R n := fun h => hgood (Or.inl h)
      have hnotQ : clocks ∉ Q n := fun h => hgood (Or.inr h)
      let x := deletedEmpiricalArrival removed clocks t
      have hx0 : 0 ≤ x := deletedEmpiricalArrival_nonneg removed clocks t
      have hx1 : x < 1 := htα.trans_lt hα
      have hqx0 : 0 ≤ q x := profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hx0, hx1⟩
      have hqxα : q x ≤ q α := (strictMonoOn_profileQuantile hf.integrable hf.ae_pos).monotoneOn
        ⟨hx0, hx1⟩ ⟨hα0, hα⟩ htα
      have hqerr : |t - q x| < δ :=
        lt_of_not_ge fun h => hnotQ ⟨removed, hr, t, ht0, htα, h⟩
      have htT : t ≤ T := by
        have h := (abs_lt.mp hqerr).2
        have hδ1 : δ ≤ 1 := min_le_right _ _
        dsimp [T]
        linarith
      have hqxT : q x ≤ T := by dsimp [T]; linarith
      have hdist : dist t (q x) < a := by
        rw [Real.dist_eq]
        exact hqerr.trans_le (min_le_left _ _)
      have hDerr : |D t - D (q x)| < ε / 2 := by
        simpa only [Real.dist_eq] using hmod t ⟨ht0, htT⟩ (q x) ⟨hqx0, hqxT⟩ hdist
      have hRerr : |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t - D t| < ε / 2 :=
        lt_of_not_ge fun h => hnotR ⟨removed, hr, t, ⟨ht0, htT⟩, h⟩
      have htri := abs_sub_le (deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t)
        (D t) (D (q x))
      change ε ≤ |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t - D (q x)| at hbad
      linarith
    have hlim := hR.add hQ
    simp only [add_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hbound
  · have hempty (n : ℕ) :
        {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
          ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
            ε ≤ |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t -
              profileD profileMeasure f (profileQuantile profileMeasure f
                (deletedEmpiricalArrival removed clocks t))|} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro clocks ⟨removed, _, t, _, htα, _⟩
      exact hα0 ((deletedEmpiricalArrival_nonneg removed clocks t).trans htα)
    simp_rw [hempty, measure_empty]
    exact tendsto_const_nhds

/-- Original-row version of both deleted-chain order-statistic conclusions.
The exact count formula above identifies the spatial coordinate at each
unmarked arrival as `q/n`; the omitted empty initial row is restored here. -/
theorem section5_deleted_order_statistics
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ removed : Finset (Fin n), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |t - profileQuantile profileMeasure f
            (deletedEmpiricalArrival removed clocks t)|}) atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ removed : Finset (Fin n), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |deletedEmpiricalRemainingGe (w n) removed clocks t -
            profileD profileMeasure f (profileQuantile profileMeasure f
              (deletedEmpiricalArrival removed clocks t))|}) atTop (𝓝 0)) := by
  constructor
  · intro ε hε
    exact (tendsto_add_atTop_iff_nat 1).mp
      (section5_uniform_deleted_quantile w f hf r hα ε hε)
  · intro ε hε
    exact (tendsto_add_atTop_iff_nat 1).mp
      (section5_uniform_deleted_denominator w f hnorm hf r hα ε hε)

/-- The normalized total unmarked rate strictly after time `t`. At an
unmarked arrival this is exactly the denominator governing the next gap. -/
def deletedEmpiricalRemaining {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ removed, if t < clocks i then w.rate i else 0) / n

/-- With distinct clocks, passing from weak to strict survival removes at
most the single ringing clock, uniformly over times and deleted sets. -/
lemma deleted_remaining_weak_strict_error (w : WeightArray) (n : ℕ)
    (removed : Finset (Fin (n + 1))) (clocks : Fin (n + 1) → ℝ)
    (hinj : Function.Injective clocks) (t : ℝ) :
    |deletedEmpiricalRemaining (w (n + 1)) removed clocks t -
      deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t| ≤
        rowMaxRate w n / (n + 1 : ℕ) := by
  classical
  have hmax : 0 ≤ rowMaxRate w n :=
    ((w (n + 1)).positive 0).le.trans (rate_le_rowMaxRate w n 0)
  have hterm (i : Fin (n + 1)) :
      (if t ≤ clocks i then (w (n + 1)).rate i else 0) -
        (if t < clocks i then (w (n + 1)).rate i else 0) =
          if clocks i = t then (w (n + 1)).rate i else 0 := by
    by_cases he : clocks i = t
    · simp [he]
    · by_cases ht : t < clocks i
      · simp [ht, ht.le, he]
      · have hh : clocks i < t := lt_of_le_of_ne (le_of_not_gt ht) he
        simp [not_le.mpr hh, ht, he]
  rw [abs_sub_comm, deletedEmpiricalRemainingGe, deletedEmpiricalRemaining,
    ← sub_div, ← Finset.sum_sub_distrib]
  simp_rw [hterm]
  have hnonneg : 0 ≤ ∑ i ∈ Finset.univ \ removed,
      if clocks i = t then (w (n + 1)).rate i else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact (w (n + 1)).positive i |>.le
    · exact le_rfl
  rw [abs_of_nonneg (div_nonneg hnonneg (by positivity))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  by_cases hex : ∃ i, clocks i = t
  · obtain ⟨i, hi⟩ := hex
    have heq (j : Fin (n + 1)) : clocks j = t ↔ j = i := by
      rw [← hi]
      exact hinj.eq_iff
    simp_rw [heq]
    simp only [Finset.sum_ite_eq', Finset.mem_sdiff, Finset.mem_univ, true_and]
    split_ifs
    · exact hmax
    · exact rate_le_rowMaxRate w n i
  · have heq (i : Fin (n + 1)) : clocks i ≠ t := fun hi => hex ⟨i, hi⟩
    simpa only [heq, if_false, Finset.sum_const_zero] using hmax

/-- The actual post-arrival deleted-chain denominator `W_q°/n` converges
uniformly to `D(t_(q/n))`. Weak/strict survival is accounted for explicitly.
This is still a macroscopic rate limit, not a statement about gap moments. -/
theorem section5_deleted_gap_rate
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ removed : Finset (Fin n), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |deletedEmpiricalRemaining (w n) removed clocks t -
            profileD profileMeasure f (profileQuantile profileMeasure f
              (deletedEmpiricalArrival removed clocks t))|}) atTop (𝓝 0) := by
  intro ε hε
  apply (tendsto_add_atTop_iff_nat 1).mp
  have he : ∀ᶠ n : ℕ in atTop, rowMaxRate w n / (n + 1 : ℕ) < ε / 2 :=
    hf.max_weight_div_tendsto_zero.eventually (gt_mem_nhds (half_pos hε))
  have hbound : ∀ᶠ n : ℕ in atTop, exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |deletedEmpiricalRemaining (w (n + 1)) removed clocks t -
            profileD profileMeasure f (profileQuantile profileMeasure f
              (deletedEmpiricalArrival removed clocks t))|} ≤
      exponentialRace (w (n + 1))
        {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
          ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
            ε / 2 ≤ |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t -
              profileD profileMeasure f (profileQuantile profileMeasure f
                (deletedEmpiricalArrival removed clocks t))|} := by
    filter_upwards [he] with n hn
    apply measure_mono_ae
    filter_upwards [exponentialRace_injective_ae (w (n + 1))] with clocks hinj
    rintro ⟨removed, hr, t, ht0, htα, hbad⟩
    refine ⟨removed, hr, t, ht0, htα, ?_⟩
    have hdel := deleted_remaining_weak_strict_error w n removed clocks hinj t
    have htri := abs_sub_le (deletedEmpiricalRemaining (w (n + 1)) removed clocks t)
      (deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t)
      (profileD profileMeasure f (profileQuantile profileMeasure f
        (deletedEmpiricalArrival removed clocks t)))
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (section5_uniform_deleted_denominator w f hnorm hf r hα (ε / 2) (half_pos hε))
    (Eventually.of_forall fun _ => bot_le) hbound

end Luce
