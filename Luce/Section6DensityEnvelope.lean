import Luce.Section6SingleReplacement
import Luce.Section6CoordinateIntegration
import Mathlib.Probability.HasLaw

/-!
# Lemma 6.6: an integrable density envelope

The proof fixes a common background and replaces only the candidate root's
clock by a deterministic time. The number of successful roots is at most
`3^ell`. Single-coordinate integration and Tonelli then integrate this bound
against the common density envelope. All tie and integrability obligations
are proved from the clock laws.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- Vertices in `S` belonging to cycles of exactly the specified length.
Labels are zero based in Lean; the rank permutation has the same convention. -/
def exactCycleVertexCount {n : ℕ} (R : Equiv.Perm (Fin n)) (ell : ℕ)
    (S : Finset (Fin n)) : ℕ :=
  (S.filter fun i => minimalPeriod (R : Fin n → Fin n) i = ell).card

lemma measurable_exactCycleVertexCount {n : ℕ} (ell : ℕ) (S : Finset (Fin n)) :
    Measurable (fun x : Fin n → ℝ => exactCycleVertexCount (raceRankPermutation x) ell S) := by
  let F := fun R : Fin n → Fin n => (S.filter fun i => minimalPeriod R i = ell).card
  exact (measurable_of_countable F).comp measurable_raceRankPermutation_function

lemma exactCycleVertexCount_le {n : ℕ} (R : Equiv.Perm (Fin n))
    (ell : ℕ) (S : Finset (Fin n)) : exactCycleVertexCount R ell S ≤ S.card :=
  Finset.card_filter_le _ _

/-- Measure-valued version: only the selected marginal laws must be
dominated. The background laws may be arbitrary atomless probability laws. -/
theorem cycle_vertex_envelope_lintegral {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (ν : Measure ℝ) [SFinite ν] (S : Finset (Fin n)) (k : ℕ)
    (hdom : ∀ i ∈ S, μ i ≤ ν) :
    (∫⁻ x, (exactCycleVertexCount (raceRankPermutation x) (k+1) S : ℝ≥0∞)
      ∂Measure.pi μ) ≤ (3^(k+1) : ℕ) * ν univ := by
  let f : Fin n → (Fin n → ℝ) → ℝ≥0∞ := fun i x =>
    if minimalPeriod (raceRankPermutation x : Fin n → Fin n) i = k+1 then 1 else 0
  have hf (i : Fin n) : Measurable (f i) :=
    Measurable.ite (measurableSet_cycle_period i k) measurable_const measurable_const
  have hs (S' : Finset (Fin n)) (x : Fin n → ℝ) :
      (exactCycleVertexCount (raceRankPermutation x) (k+1) S' : ℝ≥0∞) = ∑ i ∈ S', f i x := by
    simp only [exactCycleVertexCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, f]
  simp_rw [hs]
  apply single_coordinate_sum_bound μ ν S f hf hdom
  intro t
  filter_upwards [independent_real_coordinates_injective_ae μ,
    independent_real_coordinates_avoid_ae μ t] with x hx ht
  calc
    _ ≤ ∑ i : Fin n, f i (update x i t) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ = ((Finset.univ.filter fun i =>
        minimalPeriod (raceRankPermutation (update x i t) : Fin n → Fin n) i = k+1).card : ℝ≥0∞) := by
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, f]
    _ ≤ _ := by exact_mod_cast single_replacement_cycle_count_le (k := k) x hx t ht

/-- Product-law form of Lemma 6.6 with the explicit universal constant.
The densities are nonnegative extended-real functions. Absence of atoms
follows from the density representation, without a separate hypothesis. -/
theorem density_envelope_product {n : ℕ} (g : Fin n → ℝ → ℝ≥0∞)
    [∀ i, IsProbabilityMeasure (volume.withDensity (g i))]
    (S : Finset (Fin n)) (ell : ℕ) (hell : 1 ≤ ell)
    (h : ℝ → ℝ) (hh0 : ∀ᵐ t ∂volume, 0 ≤ h t) (hh : Integrable h)
    (hdom : ∀ i ∈ S, ∀ᵐ t ∂volume, g i t ≤ ENNReal.ofReal (h t)) :
    (∫ x, (exactCycleVertexCount (raceRankPermutation x) ell S : ℝ)
      ∂Measure.pi (fun i => volume.withDensity (g i))) ≤ (3 : ℝ)^ell * ∫ t, h t := by
  let μ := fun i => volume.withDensity (g i)
  let ν := volume.withDensity (fun t => ENNReal.ofReal (h t))
  have hmass : ν univ = ENNReal.ofReal (∫ t, h t) := by
    rw [show ν univ = ∫⁻ t, ENNReal.ofReal (h t) by
      simp [ν, withDensity_apply _ MeasurableSet.univ]]
    exact (ofReal_integral_eq_lintegral_ofReal hh hh0).symm
  have hfinite : (∫⁻ t, ENNReal.ofReal (h t)) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hh hh0]
    exact ENNReal.ofReal_ne_top
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfinite
  cases ell with
  | zero => omega
  | succ k =>
    have hbound := cycle_vertex_envelope_lintegral μ ν S k
      (fun i hi => withDensity_mono (hdom i hi))
    have hm : Measurable (fun x : Fin n → ℝ =>
        (exactCycleVertexCount (raceRankPermutation x) (k+1) S : ℝ)) :=
      (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
        (measurable_exactCycleVertexCount (k+1) S)
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))
      hm.aestronglyMeasurable]
    simp only [ENNReal.ofReal_natCast]
    have hb := ENNReal.toReal_mono (by rw [hmass]; finiteness) hbound
    rw [ENNReal.toReal_mul, hmass, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hh0)] at hb
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hb

/-- Lemma 6.6 on an arbitrary probability space, with `K_ell = 3^ell`.
`HasLaw ... (volume.withDensity (g i))` states that clock `i` has density
`g i`; no smoothness, positivity, exponential form, or profile is required.
Domination and envelope nonnegativity may hold merely almost everywhere. -/
theorem integrable_density_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (E : Fin n → Ω → ℝ) (g : Fin n → ℝ → ℝ≥0∞)
    (hLaw : ∀ i, HasLaw (E i) (volume.withDensity (g i)) P)
    (hIndependent : iIndepFun E P) (S : Finset (Fin n))
    (ell : ℕ) (hell : 1 ≤ ell) (h : ℝ → ℝ)
    (hh0 : ∀ᵐ t ∂volume, 0 ≤ h t) (hh : Integrable h)
    (hdom : ∀ i ∈ S, ∀ᵐ t ∂volume, g i t ≤ ENNReal.ofReal (h t)) :
    Integrable (fun ω => (exactCycleVertexCount
      (raceRankPermutation (fun i => E i ω)) ell S : ℝ)) P ∧
    (∫ ω, (exactCycleVertexCount (raceRankPermutation (fun i => E i ω)) ell S : ℝ) ∂P)
      ≤ (3 : ℝ)^ell * ∫ t, h t := by
  let μ := fun i => volume.withDensity (g i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    (hLaw i).isProbabilityMeasure_iff.mp inferInstance
  have hJoint : HasLaw (fun ω i => E i ω) (Measure.pi μ) P :=
    hIndependent.hasLaw_pi hLaw
  have hm : Measurable (fun x : Fin n → ℝ =>
      (exactCycleVertexCount (raceRankPermutation x) ell S : ℝ)) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
      (measurable_exactCycleVertexCount ell S)
  have hmP := hm.aemeasurable.comp_aemeasurable hJoint.aemeasurable
  refine ⟨Integrable.of_bound hmP.aestronglyMeasurable (S.card : ℝ) ?_, ?_⟩
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast exactCycleVertexCount_le (raceRankPermutation (fun i => E i ω)) ell S
  · have he := hJoint.integral_comp hm.aestronglyMeasurable
    change (∫ ω, (exactCycleVertexCount (raceRankPermutation (fun i => E i ω)) ell S : ℝ) ∂P) = _ at he
    rw [he]
    exact density_envelope_product g S ell hell h hh0 hh hdom

end Luce.Section6
