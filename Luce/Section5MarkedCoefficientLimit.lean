import Luce.Section5GapCoefficientLimit
import Luce.Section5GapCoefficient

/-!
# Uniform coefficients at the prescribed marked ranks

The deleted gap index is `q=j-a`, so its lower endpoint has empirical
coordinate `q/n`. The paper's target is `(j+1)/n` in zero-based Lean rank
notation. Compact uniform continuity accounts for this displacement of
at most `r/n` before the coefficient is used in an expectation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Luce
attribute [local instance] Classical.propDecidable

def profileGapCoefficient (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  rateKernel (profileQuantile profileMeasure f x) a /
    profileD profileMeasure f (profileQuantile profileMeasure f x)

lemma continuousOn_profileGapCoefficient {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) (M : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => profileGapCoefficient f z.1 z.2)
      (Icc (0 : ℝ) M ×ˢ Icc (0 : ℝ) α) := by
  have hq : ContinuousOn (profileQuantile profileMeasure f) (Icc (0 : ℝ) α) :=
    (continuousOn_profileQuantile hf.integrable hf.ae_pos).mono
      (fun _ hx => ⟨hx.1, hx.2.trans_lt hα⟩)
  have hQ : ContinuousOn (fun z : ℝ × ℝ => profileQuantile profileMeasure f z.2)
      (Icc (0 : ℝ) M ×ˢ Icc (0 : ℝ) α) :=
    hq.comp continuous_snd.continuousOn (fun _ hz => hz.2)
  have hD : ContinuousOn (fun z : ℝ × ℝ =>
      profileD profileMeasure f (profileQuantile profileMeasure f z.2))
      (Icc (0 : ℝ) M ×ˢ Icc (0 : ℝ) α) :=
    (continuousOn_profileD hf.integrable hf.ae_nonneg).comp hQ
      (fun _ hz => profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hz.2.1, hz.2.2.trans_lt hα⟩)
  unfold profileGapCoefficient rateKernel
  apply (continuous_fst.continuousOn.mul
    (Real.continuous_exp.comp_continuousOn (hQ.neg.mul continuous_fst.continuousOn))).div hD
  intro z hz
  exact (profileD_pos hf.integrable hf.ae_pos
    (profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hz.2.1, hz.2.2.trans_lt hα⟩)).ne'

lemma profileGapCoefficient_uniform_rank_modulus {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc (0 : ℝ) M, ∀ x ∈ Icc (0 : ℝ) α,
      ∀ y ∈ Icc (0 : ℝ) α, |x - y| < δ →
        |profileGapCoefficient f a x - profileGapCoefficient f a y| < ε := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      (continuousOn_profileGapCoefficient hf hα M)) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro a ha x hx y hy hxy
  have hd : dist (a, x) (a, y) < δ := by simpa [Prod.dist_eq, Real.dist_eq] using hxy
  simpa only [Real.dist_eq] using hmod (a, x) ⟨ha, hx⟩ (a, y) ⟨ha, hy⟩ hd

def DeletedShiftedCoefficientBad {n : ℕ} (w : Weights n) (f : ℝ → ℝ)
    (r : ℕ) (α M ε : ℝ) (old : Fin n → ℝ) : Prop :=
  ∃ removed : Finset (Fin n), removed.card ≤ r ∧
    ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed old t ≤ α ∧
      ∃ a ∈ Icc (0 : ℝ) M, ∃ y ∈ Icc (0 : ℝ) α,
        |deletedEmpiricalArrival removed old t - y| ≤ (r : ℝ) / n ∧
          ε ≤ |rateKernel t a / deletedEmpiricalRemaining w removed old t -
            profileGapCoefficient f a y|

/-- The finite deleted-rank shift is uniform over all actual configurations. -/
theorem section5_uniform_shifted_gap_coefficient
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {old | DeletedShiftedCoefficientBad (w n) f r α M ε old}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := profileGapCoefficient_uniform_rank_modulus hf hα M (half_pos hε)
  have hsmall : ∀ᶠ n : ℕ in atTop, (r : ℝ) / n < δ :=
    ((tendsto_const_nhds (x := (r : ℝ))).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (gt_mem_nhds hδ)
  have hbound : ∀ᶠ n : ℕ in atTop,
      exponentialRace (w n) {old | DeletedShiftedCoefficientBad (w n) f r α M ε old} ≤
        exponentialRace (w n) {old | DeletedCoefficientBad (w n) f r α M (ε / 2) old} := by
    filter_upwards [hsmall] with n hn
    apply measure_mono
    rintro old ⟨removed, hr, t, ht0, htα, a, ha, y, hy, hxy, hbad⟩
    refine ⟨removed, hr, t, ht0, htα, a, ha, ?_⟩
    have hdet := hmod a ha _ ⟨deletedEmpiricalArrival_nonneg removed old t, htα⟩ y hy
      (hxy.trans_lt hn)
    have htri := abs_sub_le (rateKernel t a / deletedEmpiricalRemaining (w n) removed old t)
      (profileGapCoefficient f a (deletedEmpiricalArrival removed old t))
      (profileGapCoefficient f a y)
    change ε / 2 ≤ |rateKernel t a / deletedEmpiricalRemaining (w n) removed old t -
      profileGapCoefficient f a (deletedEmpiricalArrival removed old t)|
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (section5_uniform_deleted_gap_coefficient w f hnorm hf r hα M hM (ε / 2) (half_pos hε))
    (Eventually.of_forall fun _ => bot_le) hbound

/-- One coordinate of the actual finite marked-gap coefficient. -/
def markedGapScalar {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (old : Fin n → ℝ) (i : Fin n) (q : Fin (Finset.univ \ removed).card) : ℝ :=
  rateKernel (raceGapStart (compactDeletedClocks removed old) q) (w.rate i) /
    (raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) q / n)

lemma markedGapCoefficient_eq_prod_scalar {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n)
    (q : Fin r → Fin (Finset.univ \ removed).card) (old : Fin n → ℝ) :
    markedGapCoefficient w removed u q old = ∏ a, markedGapScalar w removed old (u a) (q a) := rfl

/-- Explicit finite validity conditions for the coefficient estimate.
This does not assert injectivity or assume any probability estimate. -/
def ValidMarkedGapConfiguration {n r : ℕ} (w : Weights n) (α M : ℝ)
    (removed : Finset (Fin n)) (u j : Fin r → Fin n)
    (q : Fin r → Fin (Finset.univ \ removed).card) : Prop :=
  removed.card ≤ r ∧ ∀ a, (q a).val + a.val = (j a).val ∧
    (j a).val + (1 : ℝ) ≤ α * n ∧ w.rate (u a) ≤ M

def MarkedCoefficientBad {n : ℕ} (w : Weights n) (f : ℝ → ℝ)
    (r : ℕ) (α M ε : ℝ) (old : Fin n → ℝ) : Prop :=
  ∃ removed : Finset (Fin n), ∃ u j : Fin r → Fin n,
    ∃ q : Fin r → Fin (Finset.univ \ removed).card,
      ValidMarkedGapConfiguration w α M removed u j q ∧
        ∃ a, ε ≤ |markedGapScalar w removed old (u a) (q a) -
          profileGapCoefficient f (w.rate (u a)) (((j a).val + (1 : ℝ)) / n)|

lemma marked_raceGapStart_eq_consecutiveGapLower {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (q : Fin m) :
    raceGapStart times q = consecutiveGapLower times htimes q := by
  rw [raceGapStart, raceDraw_eq times htimes, consecutiveGapLower_eq_previous]

lemma markedGapScalar_eq_deleted {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (old : Fin n → ℝ) (hold : Injective old) (hpos : ∀ i, 0 < old i)
    (i : Fin n) (q : Fin (Finset.univ \ removed).card) :
    markedGapScalar w removed old i q =
      rateKernel (consecutiveGapLower (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold) q) (w.rate i) /
      deletedEmpiricalRemaining w removed old
        (consecutiveGapLower (compactDeletedClocks removed old)
          (compactDeletedClocks_injective removed old hold) q) := by
  rw [markedGapScalar, marked_raceGapStart_eq_consecutiveGapLower _
    (compactDeletedClocks_injective removed old hold), deletedEmpiricalRemaining_gapLower w removed old hold hpos]
  unfold raceGapRate
  rw [raceDraw_eq _ (compactDeletedClocks_injective removed old hold)]

/-- Exact finite arithmetic at the marked gap's lower endpoint. -/
lemma validMarkedGap_coordinates {n r : ℕ} (w : Weights n) (hn : 0 < n)
    {α M : ℝ} (removed : Finset (Fin n)) (u j : Fin r → Fin n)
    (q : Fin r → Fin (Finset.univ \ removed).card)
    (hv : ValidMarkedGapConfiguration w α M removed u j q)
    (old : Fin n → ℝ) (hold : Injective old) (hpos : ∀ i, 0 < old i) (a : Fin r) :
    let t := consecutiveGapLower (compactDeletedClocks removed old)
      (compactDeletedClocks_injective removed old hold) (q a)
    0 ≤ t ∧ deletedEmpiricalArrival removed old t ≤ α ∧
      (((j a).val + (1 : ℝ)) / n) ∈ Icc (0 : ℝ) α ∧
      |deletedEmpiricalArrival removed old t - (((j a).val + (1 : ℝ)) / n)| ≤ (r : ℝ) / n := by
  dsimp only
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq : ((q a).val : ℝ) + a.val = (j a).val := by exact_mod_cast (hv.2 a).1
  have hj := (hv.2 a).2.1
  have ha : (a.val : ℝ) + 1 ≤ r := by exact_mod_cast a.isLt
  refine ⟨consecutiveGapLower_nonneg _ _ (fun k => (hpos _).le) _, ?_, ?_, ?_⟩
  · rw [deletedEmpiricalArrival_gapLower removed old hold hpos, div_le_iff₀ hN]
    linarith
  · exact ⟨div_nonneg (by positivity) hN.le, (div_le_iff₀ hN).mpr hj⟩
  · rw [deletedEmpiricalArrival_gapLower removed old hold hpos, ← sub_div,
      abs_div, abs_of_pos hN]
    apply div_le_div_of_nonneg_right _ hN.le
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Every bounded sorted marked configuration is controlled by one global
bad event. The probability tends to zero uniformly over all configurations
and all marked coordinates, at the original prescribed rank `(j+1)/n`. -/
theorem section5_uniform_marked_gap_coefficient
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {old | MarkedCoefficientBad (w n) f r α M ε old}) atTop (𝓝 0) := by
  intro ε hε
  have hbound : ∀ᶠ n : ℕ in atTop,
      exponentialRace (w n) {old | MarkedCoefficientBad (w n) f r α M ε old} ≤
        exponentialRace (w n) {old | DeletedShiftedCoefficientBad (w n) f r α M ε old} := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    apply measure_mono_ae
    filter_upwards [exponentialRace_injective_ae (w n), exponentialRace_positive_background (w n)] with old hold hpos
    rintro ⟨removed, u, j, q, hv, a, hbad⟩
    let t := consecutiveGapLower (compactDeletedClocks removed old)
      (compactDeletedClocks_injective removed old hold) (q a)
    obtain ⟨ht0, htα, hy, hshift⟩ := validMarkedGap_coordinates (w n) hn removed u j q hv old hold hpos a
    refine ⟨removed, hv.1, t, ht0, htα, (w n).rate (u a),
      ⟨((w n).positive _).le, (hv.2 a).2.2⟩, ((j a).val + (1 : ℝ)) / n, hy, hshift, ?_⟩
    rwa [markedGapScalar_eq_deleted (w n) removed old hold hpos] at hbad
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (section5_uniform_shifted_gap_coefficient w f hnorm hf r hα M hM ε hε)
    (Eventually.of_forall fun _ => bot_le) hbound

/-- A fixed deterministic envelope for both actual and target scalar
coefficients. Every probabilistic background satisfies the two explicit
clock conditions almost surely under the proved exponential law. -/
theorem ProfileLimit.marked_gap_scalar_uniform_bound {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ removed : Finset (Fin n), ∀ u j : Fin r → Fin n,
        ∀ q : Fin r → Fin (Finset.univ \ removed).card,
          ValidMarkedGapConfiguration (w n) α M removed u j q →
            ∀ old : Fin n → ℝ, Injective old → (∀ i, 0 < old i) → ∀ a,
              |markedGapScalar (w n) removed old (u a) (q a)| ≤ C ∧
              |profileGapCoefficient f ((w n).rate (u a)) (((j a).val + (1 : ℝ)) / n)| ≤ C := by
  by_cases hα0 : 0 ≤ α
  · obtain ⟨b₀, hb₀, hW⟩ := hf.deleted_remaining_uniform_lower r hα
    let Dα := profileD profileMeasure f (profileQuantile profileMeasure f α)
    obtain ⟨hDα, hD⟩ := section3_denominator_lower hf hα0 hα
    let b := min b₀ Dα
    have hb : 0 < b := lt_min hb₀ hDα
    refine ⟨M / b + 1, by positivity, ?_⟩
    filter_upwards [hW, eventually_gt_atTop 0] with n hn hn0
    intro removed u j q hv old hold hpos a
    obtain ⟨ht0, htα, hy, _⟩ := validMarkedGap_coordinates (w n) hn0 removed u j q hv old hold hpos a
    let t := consecutiveGapLower (compactDeletedClocks removed old)
      (compactDeletedClocks_injective removed old hold) (q a)
    have hbW : b ≤ deletedEmpiricalRemaining (w n) removed old t :=
      (min_le_left b₀ Dα).trans (hn removed hv.1 old t htα)
    have hbD : b ≤ profileD profileMeasure f
        (profileQuantile profileMeasure f (((j a).val + (1 : ℝ)) / n)) :=
      (min_le_right b₀ Dα).trans (hD _ hy)
    have hrate := ((w n).positive (u a)).le
    have hrateM := (hv.2 a).2.2
    have hqt0 := profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hy.1, hy.2.trans_lt hα⟩
    rw [markedGapScalar_eq_deleted (w n) removed old hold hpos]
    constructor
    · rw [abs_of_nonneg (div_nonneg (rateKernel_nonneg hrate) (hb.trans_le hbW).le)]
      have hle := div_le_div₀ hM ((rateKernel_le ht0 hrate).trans hrateM) hb hbW
      exact hle.trans (by linarith)
    · unfold profileGapCoefficient
      rw [abs_of_nonneg (div_nonneg (rateKernel_nonneg hrate) (hb.trans_le hbD).le)]
      have hle := div_le_div₀ hM ((rateKernel_le hqt0 hrate).trans hrateM) hb hbD
      exact hle.trans (by linarith)
  · refine ⟨1, zero_lt_one, Eventually.of_forall ?_⟩
    intro n removed u j q hv old hold hpos a
    have hj := (hv.2 a).2.1
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnonpos : α * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hα0) hn
    have hi : (0 : ℝ) ≤ (j a).val := Nat.cast_nonneg _
    exfalso
    linarith

end Luce
