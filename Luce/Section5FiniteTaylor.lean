import Luce.Section5GapCoefficient
import Luce.Section5MarkedGapBridge

/-!
# Finite, uniform Taylor bound for actual marked-rank probabilities

Source: `fixed_points.tex:1035–1048`. The exact deleted-clock insertion
identity is expanded using the actual normalized gaps. The deterministic
suffix-rate bound is the finite reservoir input, and all random integrals
and mixed moments are proved before the real expectations are compared.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators

namespace Luce

lemma raceGapStart_eq_consecutiveGapLower {m : ℕ} (c : Fin m → ℝ)
    (hc : Injective c) (q : Fin m) :
    raceGapStart c q = consecutiveGapLower c hc q := by
  rw [raceGapStart, raceDraw_eq c hc, consecutiveGapLower_eq_previous]

lemma raceGapDuration_eq_normalized_div_rate {m : ℕ} (w : Weights m)
    (c : Fin m → ℝ) (hc : Injective c) (q : Fin m) :
    arrivalTime c hc q - consecutiveGapLower c hc q =
      raceNormalizedGaps w c q / raceGapRate w c q := by
  rw [raceNormalizedGaps, raceGapRate, raceDraw_eq c hc,
    ← ordered_gap_eq_normalized_div_rate, consecutiveGapLower_eq_previous]
  rfl

lemma raceNormalizedGaps_nonneg {m : ℕ} (w : Weights m)
    (c : Fin m → ℝ) (hc : Injective c) (hpos : ∀ i, 0 ≤ c i) (q : Fin m) :
    0 ≤ raceNormalizedGaps w c q := by
  rw [raceNormalizedGaps, raceDraw_eq c hc, orderedNormalizedGaps_eq_rate_mul_gap,
    ← consecutiveGapLower_eq_previous]
  exact mul_nonneg (orderedRemainingRate_pos w _ q).le
    (sub_nonneg.mpr (consecutiveGapLower_le_upper c hc hpos q))

lemma deletedGapKernel_eq_normalizedGapMass {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hold : Injective old)
    (hpos : ∀ i, 0 ≤ old i) (i : Fin n) (q : Fin (Finset.univ \ removed).card) :
    (deletedGapKernel w removed old i q.val).toReal =
      exponentialGapMass (w.rate i)
        (raceGapStart (compactDeletedClocks removed old) q)
        (raceNormalizedGaps (compactDeletedWeights w removed) (compactDeletedClocks removed old) q /
          raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) q) := by
  rw [deletedGapKernel_toReal_eq_exponentialGapMass w removed old hold hpos,
    raceGapStart_eq_consecutiveGapLower _ (compactDeletedClocks_injective removed old hold),
    ← raceGapDuration_eq_normalized_div_rate _ _ (compactDeletedClocks_injective removed old hold)]

/-- The pointwise rescaled Taylor remainder, with the source's actual
deleted gap masses and coefficients. No probability or conditional law is
assumed here. The raw gap length is replaced using its proved identity. -/
theorem markedGap_taylor_pointwise {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n)
    (q : Fin r → Fin (Finset.univ \ removed).card) {b M : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hM : 0 ≤ M) (huM : ∀ a, w.rate (u a) ≤ M)
    (hW : ∀ σ : Equiv.Perm (Fin (Finset.univ \ removed).card), ∀ a,
      b * n ≤ orderedRemainingRate (compactDeletedWeights w removed) σ (q a))
    (old : Fin n → ℝ) (hold : Injective old) (hpos : ∀ i, 0 ≤ old i) :
    |(n : ℝ) ^ r * (∏ a, (deletedGapKernel w removed old (u a) (q a).val).toReal) -
      markedGapCoefficient w removed u q old * (∏ a, markedNormalizedGaps w removed q old a)| ≤
      ((M / b) ^ (r + 1) / n) *
        ((∑ a, markedNormalizedGaps w removed q old a) * ∏ a, markedNormalizedGaps w removed q old a) := by
  let c := compactDeletedClocks removed old
  let v := compactDeletedWeights w removed
  have hc : Injective c := compactDeletedClocks_injective removed old hold
  have hs (a : Fin r) : 0 ≤ raceGapStart c (q a) := by
    rw [raceGapStart_eq_consecutiveGapLower c hc]
    exact consecutiveGapLower_nonneg c hc (fun i => hpos _) _
  have hξ (a : Fin r) : 0 ≤ raceNormalizedGaps v c (q a) :=
    raceNormalizedGaps_nonneg v c hc (fun i => hpos _) _
  have ht := rescaled_prod_exponentialGapMass_taylor
    (fun a => w.rate (u a)) (fun a => raceGapStart c (q a))
    (fun a => raceGapRate v c (q a)) (fun a => raceNormalizedGaps v c (q a))
    (Nat.cast_pos.mpr hn) hb hM (fun a => (w.positive (u a)).le) huM hs
    (hW (raceDraw c)) hξ
  rw [rescaled_gap_error_constant (Nat.cast_pos.mpr hn) hb] at ht
  simpa only [deletedGapKernel_eq_normalizedGapMass w removed old hold hpos,
    markedGapCoefficient, markedNormalizedGaps, c, v] using ht

/-- The finite Taylor error after averaging the actual deleted race.
Distinct gaps enter only through their proved Exp(1) mixed moments. -/
theorem markedGap_taylor_expectation {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n)
    (q : Fin r ↪ Fin (Finset.univ \ removed).card) {b M : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hM : 0 ≤ M) (huM : ∀ a, w.rate (u a) ≤ M)
    (hW : ∀ σ : Equiv.Perm (Fin (Finset.univ \ removed).card), ∀ a,
      b * n ≤ orderedRemainingRate (compactDeletedWeights w removed) σ (q a)) :
    Integrable (fun old => markedGapCoefficient w removed u q old *
      ∏ a, markedNormalizedGaps w removed q old a) (exponentialRace w) ∧
    |(n : ℝ) ^ r * (∫ old, ∏ a, (deletedGapKernel w removed old (u a) (q a).val).toReal
        ∂exponentialRace w) -
      (∫ old, markedGapCoefficient w removed u q old *
        ∏ a, markedNormalizedGaps w removed q old a ∂exponentialRace w)| ≤
      (2 * (r : ℝ) / n) * (M / b) ^ (r + 1) := by
  let F := fun old => (n : ℝ) ^ r * ∏ a, (deletedGapKernel w removed old (u a) (q a).val).toReal
  let G := fun old => markedGapCoefficient w removed u q old *
    ∏ a, markedNormalizedGaps w removed q old a
  let E := fun old => ((∑ a, markedNormalizedGaps w removed q old a) *
    ∏ a, markedNormalizedGaps w removed q old a)
  let C := (M / b) ^ (r + 1) / n
  have hiF : Integrable F (exponentialRace w) :=
    (deletedGapProduct_integrable w removed u (fun a => (q a).val)).const_mul _
  have hmG : Measurable G := (measurable_markedGapCoefficient w removed u q).mul
    (Finset.measurable_prod _ (fun a _ => (measurable_pi_apply a).comp
      (measurable_markedNormalizedGaps w removed q)))
  have hiE : Integrable E (exponentialRace w) :=
    integrable_markedNormalizedGaps_taylorEnvelope w removed q
  have hbound : ∀ᵐ old ∂exponentialRace w, |F old - G old| ≤ C * E old := by
    filter_upwards [exponentialRace_injective_ae w, exponentialRace_nonnegative_background w]
      with old hold hpos
    exact markedGap_taylor_pointwise w removed u q hn hb hM huM hW old hold hpos
  have hiErr : Integrable (fun old => F old - G old) (exponentialRace w) :=
    (hiE.const_mul C).mono' (hiF.aestronglyMeasurable.sub hmG.aestronglyMeasurable)
      (hbound.mono fun old h => by simpa only [Real.norm_eq_abs] using h)
  have hiG : Integrable G (exponentialRace w) := by
    convert hiF.sub hiErr using 1
    ext old
    change G old = F old - (F old - G old)
    ring
  refine ⟨hiG, ?_⟩
  have he : |(∫ old, F old ∂exponentialRace w) - ∫ old, G old ∂exponentialRace w| ≤
      C * (2 * (r : ℝ)) := by
    rw [← integral_sub hiF hiG]
    calc
      _ ≤ ∫ old, |F old - G old| ∂exponentialRace w := abs_integral_le_integral_abs
      _ ≤ ∫ old, C * E old ∂exponentialRace w :=
        integral_mono_ae hiErr.abs (hiE.const_mul C) hbound
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        exact integral_markedNormalizedGaps_taylorEnvelope w removed q
  have hC : C * (2 * (r : ℝ)) = (2 * (r : ℝ) / n) * (M / b) ^ (r + 1) := by
    dsimp [C]
    ring
  simpa only [F, G, integral_const_mul] using he.trans_eq hC

/-- Source 1035–1048, finite quantitative version for the actual sorted
marked-rank probability. The lower-rate bound is a finite reservoir input;
the main asymptotic theorem discharges it from the original profile limit. -/
theorem markedRankCylinder_taylor_expectation {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r ↪ Fin (Finset.univ \ Finset.univ.image u).card)
    (hq : StrictMono (fun a => (q a).val)) (hindex : ∀ a, (q a).val + a.val = (j a).val)
    {b M : ℝ} (hn : 0 < n) (hb : 0 < b) (hM : 0 ≤ M) (huM : ∀ a, w.rate (u a) ≤ M)
    (hW : ∀ σ : Equiv.Perm (Fin (Finset.univ \ Finset.univ.image u).card), ∀ a,
      b * n ≤ orderedRemainingRate (compactDeletedWeights w (Finset.univ.image u)) σ (q a)) :
    |(n : ℝ) ^ r * (exponentialRace w).real {old | MarkedRankCylinder u j old} -
      (∫ old, markedGapCoefficient w (Finset.univ.image u) u q old *
        ∏ a, markedNormalizedGaps w (Finset.univ.image u) q old a ∂exponentialRace w)| ≤
      (2 * (r : ℝ) / n) * (M / b) ^ (r + 1) := by
  rw [markedRankCylinder_real_probability_eq_deletedGapProduct w u j hu hj
    (fun a => (q a).val) hq hindex]
  exact (markedGap_taylor_expectation w (Finset.univ.image u) u q hn hb hM huM hW).2

end Luce
