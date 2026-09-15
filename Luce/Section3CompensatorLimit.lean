import Luce.Section3DenominatorReplacement
import Luce.Section3Survival
import Luce.Section3Expectation

/-!
# Proposition 3.2: the weighted interior compensator

Source: `fixed_points.tex:735–806`. The proof follows the paper's successive
denominator, survival, variance, and deterministic-integral approximations.
Every approximation theorem used here derives its estimates from the actual
profile hypothesis; no approximation is assumed in the final theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- The diagonal of the density in `eq:rho`. Its endpoint values are only
total extensions; all integrals in this section exclude zero and one. -/
def profileDiagonal (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  rateKernel (profileQuantile profileMeasure f x) (f x) /
    profileD profileMeasure f (profileQuantile profileMeasure f x)

/-- The literal signed weighted sum in `eq:weighted-compensator`. -/
def interiorCompensatorSum {n : ℕ} (w : Weights n) (g : ℝ → ℝ)
    (α : ℝ) (E : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if ((i.val : ℝ) + 1) / n ≤ α then
    g (((i.val : ℝ) + 1) / n) * predictableChance w (raceDraw E) i else 0

lemma continuousOn_compensator_coefficient {w : WeightArray} {f g : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (hg : ContinuousOn g (Icc (0 : ℝ) α)) :
    ContinuousOn (fun x => g x / profileD profileMeasure f
      (profileQuantile profileMeasure f x)) (Icc (0 : ℝ) α) := by
  have hq := (continuousOn_profileQuantile hf.integrable hf.ae_pos).mono
    (show Icc (0 : ℝ) α ⊆ Ico 0 1 from fun _ hx => ⟨hx.1, hx.2.trans_lt hα⟩)
  have hD := (continuousOn_profileD hf.integrable hf.ae_nonneg).comp hq
    (fun x hx => profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hx.1, hx.2.trans_lt hα⟩)
  exact hg.div hD fun x hx =>
    (profileD_pos hf.integrable hf.ae_pos
      (profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hx.1, hx.2.trans_lt hα⟩)).ne'

/-- The limiting integral exists as a genuine Bochner integral. -/
theorem integrable_interior_density {w : WeightArray} {f g : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (hg : ContinuousOn g (Icc (0 : ℝ) α)) :
    IntegrableOn (fun x => g x * profileDiagonal f x) (Ioc (0 : ℝ) α) := by
  by_cases hα0 : 0 ≤ α
  · have hq := (continuousOn_profileQuantile hf.integrable hf.ae_pos).mono
      (show Icc (0 : ℝ) α ⊆ Ico 0 1 from fun _ hx => ⟨hx.1, hx.2.trans_lt hα⟩)
    have h := hf.integrable_expectation_limit hα0 hα
      (continuousOn_compensator_coefficient hf hα hg) hq
      (fun x hx => profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hx.1, hx.2.trans_lt hα⟩)
    convert h using 1
    funext x
    dsimp [profileDiagonal]
    ring
  · simp [Ioc_eq_empty_of_le (lt_of_not_ge hα0).le]

/-- Proposition 3.2, equation `eq:weighted-compensator`, on the actual
exponential race. The next theorem transfers it to arbitrary row spaces. -/
theorem section3_weighted_compensator
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (0 : ℝ) α)) :
    ConvergesInProbability (fun n => exponentialRace (w (n + 1)))
      (fun n E => interiorCompensatorSum (w (n + 1)) g α E)
      (∫ x in Ioc (0 : ℝ) α, g x * profileDiagonal f x) := by
  classical
  by_cases hα0 : 0 ≤ α
  · let q := profileQuantile profileMeasure f
    let c := fun x => g x / profileD profileMeasure f (q x)
    let s := fun n => (Finset.univ : Finset (Fin (n + 1))).filter
      (fun i => ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α)
    let x := fun n (i : Fin (n + 1)) => ((i.val : ℝ) + 1) / (n + 1 : ℕ)
    have hs : ∀ n i, i ∈ s n → x n i ≤ α := fun n i hi => (Finset.mem_filter.mp hi).2
    have hx : ∀ n i, i ∈ s n → x n i ∈ Icc (0 : ℝ) α :=
      fun n i hi => ⟨by dsimp [x]; positivity, hs n i hi⟩
    have hc : ContinuousOn c (Icc (0 : ℝ) α) := continuousOn_compensator_coefficient hf hα hg
    have hq : ContinuousOn q (Icc (0 : ℝ) α) :=
      (continuousOn_profileQuantile hf.integrable hf.ae_pos).mono
        (fun _ hx => ⟨hx.1, hx.2.trans_lt hα⟩)
    obtain ⟨G, hGb⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
    have hG : 0 ≤ G := (norm_nonneg (g 0)).trans (hGb 0 ⟨le_rfl, hα0⟩)
    obtain ⟨C, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    have hC : 0 ≤ C := (norm_nonneg (c 0)).trans (hCb 0 ⟨le_rfl, hα0⟩)
    have hgb : ∀ n i, i ∈ s n → |g (x n i)| ≤ G := fun n i hi => hGb _ (hx n i hi)
    have hcb : ∀ n i, i ∈ s n → |c (x n i)| ≤ C := fun n i hi => hCb _ (hx n i hi)
    let A := fun n (E : Fin (n + 1) → ℝ) =>
      (∑ i ∈ s n, c (x n i) * (w (n + 1)).rate i * survivalGe (orderTime E i) (E i)) /
        (n + 1 : ℕ)
    let B := fun n (E : Fin (n + 1) → ℝ) =>
      (∑ i ∈ s n, c (x n i) * (w (n + 1)).rate i * survivalGe (q (x n i)) (E i)) /
        (n + 1 : ℕ)
    let M := fun n => (∑ i ∈ s n, c (x n i) * rateKernel (q (x n i)) ((w (n + 1)).rate i)) /
      (n + 1 : ℕ)
    have hM : Tendsto M atTop (𝓝 (∫ x in Ioc (0 : ℝ) α, g x * profileDiagonal f x)) := by
      have h := hf.deterministic_expectation_limit hα0 hα hc hq
        (fun y hy => profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hy.1, hy.2.trans_lt hα⟩)
      have heq : (fun y => c y * rateKernel (q y) (f y)) =
          fun y => g y * profileDiagonal f y := by
        funext y
        dsimp [c, profileDiagonal, q]
        ring
      simpa only [M, s, x, Finset.sum_filter, heq] using h
    have hB : ConvergesInProbability (fun n => exponentialRace (w (n + 1))) B
        (∫ x in Ioc (0 : ℝ) α, g x * profileDiagonal f x) := by
      apply ConvergesInProbability.of_sub (ConvergesInProbability.deterministic hM)
      exact section3_survival_fluctuation w f hf hα s (fun n i => c (x n i)) hC hs hcb
    have hA : ConvergesInProbability (fun n => exponentialRace (w (n + 1))) A
        (∫ x in Ioc (0 : ℝ) α, g x * profileDiagonal f x) := by
      apply hB.of_sub
      have h := section3_survival_replacement w f hf hα s (fun n i => c (x n i)) hC hs hcb
      simpa only [A, B, sub_div] using h
    apply hA.of_sub
    have h := denominator_replacement_converges w f hnorm hf hα s hs
      (fun n i => g (x n i)) hG hgb
    simpa only [interiorCompensatorSum, A, s, x, c, q, Finset.sum_filter] using h
  · have hαneg : α ≤ 0 := (lt_of_not_ge hα0).le
    have hzero : ∀ n E, interiorCompensatorSum (w (n + 1)) g α E = 0 := by
      intro n E
      apply Finset.sum_eq_zero
      intro i _
      have hpos : 0 < ((i.val : ℝ) + 1) / (n + 1 : ℕ) := by positivity
      exact if_neg (not_le.mpr (hαneg.trans_lt hpos))
    simp only [hzero, Ioc_eq_empty_of_le hαneg, Measure.restrict_empty, integral_zero_measure]
    exact ConvergesInProbability.deterministic tendsto_const_nhds

/-- The weighted compensator limit on arbitrary row probability spaces,
with the original unshifted row index. Independence is only within rows. -/
theorem section3_weighted_compensator_general
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n))
    {α : ℝ} (hα : α < 1) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (0 : ℝ) α)) :
    ConvergesInProbability P
      (fun n ω => interiorCompensatorSum (w n) g α (fun i => E n i ω))
      (∫ x in Ioc (0 : ℝ) α, g x * profileDiagonal f x) := by
  intro ε hε
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (section3_weighted_compensator w f hnorm hf hα g hg ε hε)
  intro n
  have hJoint : HasLaw (fun ω i => E (n + 1) i ω) (exponentialRace (w (n + 1)))
      (P (n + 1)) := (hIndependent (n + 1)).hasLaw_pi (hLaw (n + 1))
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  simpa only [hJoint.map_eq, Set.preimage_setOf_eq] using
    (Measure.le_map_apply hJoint.aemeasurable
      {e | ε < |interiorCompensatorSum (w (n + 1)) g α e -
        ∫ x in Ioc (0 : ℝ) α, g x * profileDiagonal f x|})

/-- A continuous function whose domain is literally the paper's `[0,α]`
can be used without an extra extension hypothesis. Values outside are zero. -/
def intervalTestExtension (α : ℝ) (g : Icc (0 : ℝ) α → ℝ) (x : ℝ) : ℝ :=
  if hx : x ∈ Icc (0 : ℝ) α then g ⟨x, hx⟩ else 0

lemma intervalTestExtension_eq (α : ℝ) (g : Icc (0 : ℝ) α → ℝ)
    (x : Icc (0 : ℝ) α) : intervalTestExtension α g x = g x := by
  simp [intervalTestExtension, x.property]

lemma continuousOn_intervalTestExtension (α : ℝ) (g : Icc (0 : ℝ) α → ℝ)
    (hg : Continuous g) : ContinuousOn (intervalTestExtension α g) (Icc (0 : ℝ) α) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have heq : (Icc (0 : ℝ) α).domRestrict (intervalTestExtension α g) = g := by
    funext x
    exact intervalTestExtension_eq α g x
  rwa [heq]

/-- Proposition 3.2 with a continuous test on exactly the source domain.
The extension is explicitly proved to agree on that domain above. -/
theorem section3_weighted_compensator_on_interval
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n))
    {α : ℝ} (hα : α < 1) (g : Icc (0 : ℝ) α → ℝ) (hg : Continuous g) :
    ConvergesInProbability P
      (fun n ω => interiorCompensatorSum (w n) (intervalTestExtension α g) α (fun i => E n i ω))
      (∫ x in Ioc (0 : ℝ) α, intervalTestExtension α g x * profileDiagonal f x) :=
  section3_weighted_compensator_general Ω P w f hnorm hf E hLaw hIndependent hα
    (intervalTestExtension α g) (continuousOn_intervalTestExtension α g hg)

end Luce
