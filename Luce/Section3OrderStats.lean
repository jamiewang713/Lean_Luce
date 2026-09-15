import Luce.Section3Race
import Luce.Section3Quantile
import Luce.Section1RaceOrder
import Mathlib.Order.Interval.Finset.Fin

/-!
# Uniform convergence of the exponential order statistics

This file proves `fixed_points.tex`, equation `eq:uniform-quantile`, from
the uniform empirical CDF theorem. Ties have probability zero by the actual
independent exponential law; the total order-time definition uses zero only
on that exceptional set.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- A total version of the `k+1`st order statistic. The value on tied clock
configurations is irrelevant because their probability is proved to be zero. -/
def orderTime {n : ℕ} (clocks : Fin n → ℝ) (k : Fin n) : ℝ :=
  if h : Function.Injective clocks then arrivalTime clocks h k else 0

lemma orderTime_eq_arrivalTime {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (k : Fin n) :
    orderTime clocks k = arrivalTime clocks hinj k := by
  simp [orderTime, hinj]

lemma draw_arrivalTime_le_iff {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (j k : Fin n) :
    clocks (drawPermutation clocks hinj j) ≤ arrivalTime clocks hinj k ↔ j ≤ k := by
  have hj : clockRank clocks (drawPermutation clocks hinj j) = j :=
    (rankPermutation clocks hinj).apply_symm_apply j
  have hk : clockRank clocks (drawPermutation clocks hinj k) = k :=
    (rankPermutation clocks hinj).apply_symm_apply k
  rw [arrivalTime, ← clockRank_le_iff, hj, hk]

/-- The CDF at the `k+1`st distinct arrival is exactly `(k+1)/n`. This
counts every label once by the proved draw-order permutation. -/
theorem empiricalArrival_orderTime {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (k : Fin n) :
    empiricalArrival clocks (orderTime clocks k) = ((k.val : ℝ) + 1) / n := by
  classical
  rw [orderTime_eq_arrivalTime clocks hinj k, empiricalArrival]
  congr 1
  rw [← Equiv.sum_comp (drawPermutation clocks hinj)
    (fun i => arrivalAt (arrivalTime clocks hinj k) (clocks i))]
  simp_rw [arrivalAt, draw_arrivalTime_le_iff clocks hinj]
  rw [Finset.sum_boole]
  have hs : (Finset.univ.filter (fun j : Fin n => j ≤ k)) = Finset.Iic k := by
    ext j
    simp
  rw [hs, Fin.card_Iic]
  simp

theorem exponentialRace_nonneg_ae {n : ℕ} (w : Weights n) :
    ∀ᵐ clocks ∂exponentialRace w, ∀ i, 0 ≤ clocks i := by
  apply ae_all_iff.mpr
  intro i
  apply (mem_ae_iff_prob_eq_one
    (measurableSet_le measurable_const (measurable_pi_apply i))).mpr
  simpa using exponentialRace_survival_ge w i 0 (le_refl 0)

lemma orderTime_nonneg {n : ℕ} (clocks : Fin n → ℝ)
    (hclocks : ∀ i, 0 ≤ clocks i) (k : Fin n) : 0 ≤ orderTime clocks k := by
  unfold orderTime
  split_ifs with hinj
  · exact hclocks _
  · exact le_rfl

/-- Equation `eq:uniform-quantile`, with the exact positive row shift and
one-based spatial coordinate. The proof uses the manuscript's empirical
CDF convergence and uniform continuity of its inverse. -/
theorem section3_uniform_quantile
    (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f) {α : ℝ}
    (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ |orderTime clocks k -
          profileQuantile profileMeasure f (((k.val : ℝ) + 1) / (n + 1 : ℕ))|})
      atTop (𝓝 0) := by
  intro ε hε
  by_cases hα0 : 0 ≤ α
  · obtain ⟨T, δ, hT, hδ, hmargin, hinv⟩ :=
      uniform_profile_inverse_modulus hf.integrable hf.ae_pos hα0 hα hε
    have hbound (n : ℕ) : exponentialRace (w (n + 1))
        {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
          ε ≤ |orderTime clocks k -
            profileQuantile profileMeasure f (((k.val : ℝ) + 1) / (n + 1 : ℕ))|} ≤
        exponentialRace (w (n + 1))
          {clocks | ∃ t ∈ Icc 0 T,
            δ ≤ |empiricalArrival clocks t - profileF profileMeasure f t|} := by
      apply measure_mono_ae
      filter_upwards [exponentialRace_injective_ae (w (n + 1)),
        exponentialRace_nonneg_ae (w (n + 1))] with clocks hinj hnonneg
      intro hbad
      by_contra hgood
      have herror : ∀ t ∈ Icc (0 : ℝ) T,
          |empiricalArrival clocks t - profileF profileMeasure f t| < δ := by
        intro t ht
        exact lt_of_not_ge fun h => hgood ⟨t, ht, h⟩
      obtain ⟨k, hkα, hkbad⟩ := hbad
      let x : ℝ := ((k.val : ℝ) + 1) / (n + 1 : ℕ)
      have hx0 : 0 ≤ x := by dsimp [x]; positivity
      have hτ0 := orderTime_nonneg clocks hnonneg k
      have hτcdf : empiricalArrival clocks (orderTime clocks k) = x :=
        empiricalArrival_orderTime clocks hinj k
      have hTerror := herror T ⟨hT, le_rfl⟩
      have hGT : α < empiricalArrival clocks T := by
        have := (abs_lt.mp hTerror).1
        linarith
      have hτT : orderTime clocks k ≤ T := by
        by_contra hnot
        have hmono := empiricalArrival_monotone clocks (le_of_lt (lt_of_not_ge hnot))
        rw [hτcdf] at hmono
        exact (not_le_of_gt hGT) (hmono.trans hkα)
      have herr := herror (orderTime clocks k) ⟨hτ0, hτT⟩
      rw [hτcdf, abs_sub_comm] at herr
      exact (not_lt_of_ge hkbad) (hinv x ⟨hx0, hkα⟩ (orderTime clocks k) ⟨hτ0, hτT⟩ herr)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (section3_uniform_arrival w f hf T δ hδ) (fun _ => bot_le) hbound
  · have hαneg : α < 0 := lt_of_not_ge hα0
    have hempty (n : ℕ) :
        {clocks : Fin (n + 1) → ℝ | ∃ k : Fin (n + 1),
          ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
          ε ≤ |orderTime clocks k -
            profileQuantile profileMeasure f (((k.val : ℝ) + 1) / (n + 1 : ℕ))|} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro clocks ⟨k, hk, _⟩
      have hx : 0 ≤ ((k.val : ℝ) + 1) / (n + 1 : ℕ) := by positivity
      linarith
    simp_rw [hempty, measure_empty]
    exact tendsto_const_nhds

/-- Random-time substitution in the remaining-rate process, completing
equation `eq:uniform-denominator`. The comparison times and empirical times
are confined to one compact interval before applying continuity of `D`. -/
theorem section3_uniform_denominator
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ |empiricalRemainingGe (w (n + 1)) clocks (orderTime clocks k) -
          profileD profileMeasure f
            (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / (n + 1 : ℕ)))|})
      atTop (𝓝 0) := by
  intro ε hε
  by_cases hα0 : 0 ≤ α
  · let q : ℝ → ℝ := profileQuantile profileMeasure f
    let D : ℝ → ℝ := profileD profileMeasure f
    let T : ℝ := q α + 1
    have hqα : 0 ≤ q α := profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hα0, hα⟩
    have hT : 0 ≤ T := by dsimp [T]; linarith
    have hc : ContinuousOn D (Icc 0 T) :=
      (continuousOn_profileD hf.integrable hf.ae_nonneg).mono (fun _ ht => ht.1)
    obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hc) (ε / 2) (half_pos hε)
    let δ : ℝ := min r 1
    have hδ : 0 < δ := lt_min hr zero_lt_one
    let Q (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
      {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        δ ≤ |orderTime clocks k - q (((k.val : ℝ) + 1) / (n + 1 : ℕ))|}
    let R (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
      {clocks | ∃ t ∈ Icc (0 : ℝ) T,
        ε / 2 ≤ |empiricalRemainingGe (w (n + 1)) clocks t - D t|}
    have hlimQ : Tendsto (fun n => exponentialRace (w (n + 1)) (Q n)) atTop (𝓝 0) :=
      section3_uniform_quantile w f hf hα δ hδ
    have hlimR : Tendsto (fun n => exponentialRace (w (n + 1)) (R n)) atTop (𝓝 0) :=
      section3_uniform_remaining w f hnorm hf T (ε / 2) (half_pos hε)
    have hbound (n : ℕ) : exponentialRace (w (n + 1))
        {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
          ε ≤ |empiricalRemainingGe (w (n + 1)) clocks (orderTime clocks k) -
            D (q (((k.val : ℝ) + 1) / (n + 1 : ℕ)))|} ≤
        exponentialRace (w (n + 1)) (R n) + exponentialRace (w (n + 1)) (Q n) := by
      refine (measure_mono_ae ?_).trans (measure_union_le (R n) (Q n))
      filter_upwards [exponentialRace_nonneg_ae (w (n + 1))] with clocks hnonneg
      intro hbad
      by_contra hgood
      have hnotR : clocks ∉ R n := fun h => hgood (Or.inl h)
      have hnotQ : clocks ∉ Q n := fun h => hgood (Or.inr h)
      obtain ⟨k, hkα, hkbad⟩ := hbad
      let x : ℝ := ((k.val : ℝ) + 1) / (n + 1 : ℕ)
      have hx0 : 0 ≤ x := by dsimp [x]; positivity
      have hx1 : x < 1 := hkα.trans_lt hα
      have hqx0 : 0 ≤ q x := profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hx0, hx1⟩
      have hqxα : q x ≤ q α := (strictMonoOn_profileQuantile hf.integrable hf.ae_pos).monotoneOn
        ⟨hx0, hx1⟩ ⟨hα0, hα⟩ hkα
      have hqerr : |orderTime clocks k - q x| < δ :=
        lt_of_not_ge fun h => hnotQ ⟨k, hkα, h⟩
      have hτ0 := orderTime_nonneg clocks hnonneg k
      have hτT : orderTime clocks k ≤ T := by
        have h := (abs_lt.mp hqerr).2
        have hδ1 : δ ≤ 1 := min_le_right _ _
        dsimp [T]
        linarith
      have hqxT : q x ≤ T := by dsimp [T]; linarith
      have hdist : dist (orderTime clocks k) (q x) < r := by
        rw [Real.dist_eq]
        exact hqerr.trans_le (min_le_left _ _)
      have hDerr : |D (orderTime clocks k) - D (q x)| < ε / 2 := by
        simpa only [Real.dist_eq] using
          hmod (orderTime clocks k) ⟨hτ0, hτT⟩ (q x) ⟨hqx0, hqxT⟩ hdist
      have hRerr : |empiricalRemainingGe (w (n + 1)) clocks (orderTime clocks k) -
          D (orderTime clocks k)| < ε / 2 :=
        lt_of_not_ge fun h => hnotR ⟨orderTime clocks k, ⟨hτ0, hτT⟩, h⟩
      have htri := abs_sub_le
        (empiricalRemainingGe (w (n + 1)) clocks (orderTime clocks k))
        (D (orderTime clocks k)) (D (q x))
      change ε ≤ |empiricalRemainingGe (w (n + 1)) clocks (orderTime clocks k) - D (q x)| at hkbad
      linarith
    have hlim := hlimR.add hlimQ
    simp only [add_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hbound
  · have hαneg : α < 0 := lt_of_not_ge hα0
    have hempty (n : ℕ) :
        {clocks : Fin (n + 1) → ℝ | ∃ k : Fin (n + 1),
          ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
          ε ≤ |empiricalRemainingGe (w (n + 1)) clocks (orderTime clocks k) -
            profileD profileMeasure f
              (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / (n + 1 : ℕ)))|} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro clocks ⟨k, hk, _⟩
      have hx : 0 ≤ ((k.val : ℝ) + 1) / (n + 1 : ℕ) := by positivity
      linarith
    simp_rw [hempty, measure_empty]
    exact tendsto_const_nhds

/-- The last two conclusions of Lemma 3.1 on arbitrary probability spaces,
with the original row index `n`. Independence and the exponential marginal
laws are the manuscript's race representation; no concentration conclusion
is assumed. The empty row is handled by the proved filter shift. -/
theorem section3_order_statistics_general
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) {α : ℝ} (hα : α < 1) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
        ε ≤ |orderTime (fun i => E n i ω) k -
          profileQuantile profileMeasure f (((k.val : ℝ) + 1) / n)|})
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
        ε ≤ |empiricalRemainingGe (w n) (fun i => E n i ω)
            (orderTime (fun i => E n i ω) k) -
          profileD profileMeasure f
            (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / n))|})
      atTop (𝓝 0)) := by
  have hJoint (n : ℕ) : HasLaw (fun ω i => E n i ω) (exponentialRace (w n)) (P n) :=
    (hIndependent n).hasLaw_pi (hLaw n)
  have hbound (n : ℕ) (s : Set (Fin n → ℝ)) :
      P n ((fun ω i => E n i ω) ⁻¹' s) ≤ exponentialRace (w n) s := by
    rw [← (hJoint n).map_eq]
    exact Measure.le_map_apply (hJoint n).aemeasurable s
  constructor
  · intro ε hε
    apply (tendsto_add_atTop_iff_nat 1).mp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (section3_uniform_quantile w f hf hα ε hε) (fun _ => bot_le)
      (fun n => hbound (n + 1) _)
  · intro ε hε
    apply (tendsto_add_atTop_iff_nat 1).mp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (section3_uniform_denominator w f hnorm hf hα ε hε) (fun _ => bot_le)
      (fun n => hbound (n + 1) _)

end Luce
