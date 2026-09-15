import Luce.Section3Bernoulli
import Luce.Section3LuceLaw
import Luce.Section3Intensity
import Luce.Section3PoissonCriterion

/-!
# Corollary 3.3: the interior fixed-point process

Source: `fixed_points.tex:808–819`. The actual masked fixed-point indicators
are passed to the proved predictable Poisson criterion. Its compensator and
maximum hypotheses are discharged by Proposition 3.2 under Assumption 1.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal BoundedContinuousFunction

namespace Luce

/-- The paper's one-based location, in the compact ambient interval. -/
def section3Location (n : ℕ) (k : Fin n) : Icc (0 : ℝ) 1 :=
  ⟨((k.val : ℝ) + 1) / n, by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
    constructor
    · exact div_nonneg (by positivity) hn.le
    · apply (div_le_iff₀ hn).mpr
      simpa only [one_mul] using
        (show (k.val : ℝ) + 1 ≤ n by exact_mod_cast Nat.succ_le_of_lt k.isLt)⟩

/-- The literal fixed-point process restricted to `[0,α]`, for a draw
permutation. The inverse rank convention is retained in the definition. -/
def interiorFixedPoints {n : ℕ} (α : ℝ) (π : Equiv.Perm (Fin n)) :
    FinitePointMeasure (Icc (0 : ℝ) 1) :=
  observedPointMeasure (section3Location n)
    (fun k => decide (((k.val : ℝ) + 1) / n ≤ α ∧ π.symm k = k))

/-- This representation is exactly the sum of unit Dirac masses in
`eq:fixed-process`; every selected label contributes once. -/
theorem interiorFixedPoints_toFiniteMeasure {n : ℕ} (α : ℝ)
    (π : Equiv.Perm (Fin n)) :
    (interiorFixedPoints α π).toFiniteMeasure =
      ∑ k : Fin n, if ((k.val : ℝ) + 1) / n ≤ α ∧ π.symm k = k then
        (diracProba (section3Location n k)).toFiniteMeasure else 0 := by
  simp only [interiorFixedPoints, observedPointMeasure_toFiniteMeasure,
    decide_eq_true_eq]

theorem raceInteriorBernoulli_pointMeasure {n : ℕ} (w : Weights n)
    (α : ℝ) (E : Fin n → ℝ) :
    (raceInteriorBernoulli w α).pointMeasure (section3Location n) E =
      interiorFixedPoints α (raceDraw E) := by
  unfold FiniteAdaptedBernoulli.pointMeasure interiorFixedPoints
  congr 1
  funext k
  simp only [raceInteriorBernoulli, inverse_fixed_iff]

lemma section3_convergence_congr_ae
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} {X Y : ∀ n, Ω n → ℝ} {c : ℝ}
    (hY : ConvergesInProbability P Y c) (heq : ∀ n, X n =ᵐ[P n] Y n) :
    ConvergesInProbability P X c := by
  intro ε hε
  have hmeasure (n : ℕ) :
      (P n).real {ω | ε < |X n ω - c|} =
        (P n).real {ω | ε < |Y n ω - c|} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [heq n] with ω hω
    apply propext
    change (ε < |X n ω - c|) ↔ (ε < |Y n ω - c|)
    rw [hω]
  simpa only [hmeasure] using hY ε hε

lemma section3_rowMaximum_lt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (B : BernoulliProcess P) (N : ℕ) (ω : Ω)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ k < N, B.probability k ω < ε) → B.rowMaximum N ω < ε := by
  induction N with
  | zero => intro _; exact hε
  | succ N ih =>
    intro h
    exact max_lt (ih (fun k hk => h k (Nat.lt_succ_of_lt hk)))
      (h N (Nat.lt_succ_self N))

/-- The compensator of the actual adapted indicator row agrees almost
everywhere with the explicit sum proved in Proposition 3.2. -/
theorem raceInteriorBernoulli_integral {n : ℕ} (w : Weights n) (α : ℝ)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    (fun E => ∫ y, g y ∂((raceInteriorBernoulli w α).predictableMeasure
      (section3Location n) E : Measure (Icc (0 : ℝ) 1))) =ᵐ[exponentialRace w]
    (fun E => interiorCompensatorSum w
      (fun x => g (projIcc 0 1 zero_le_one x)) α E) := by
  have hall : ∀ᵐ E ∂exponentialRace w, ∀ k : Fin n,
      (raceInteriorBernoulli w α).probability k E =
        if ((k.val : ℝ) + 1) / n ≤ α then predictableChance w (raceDraw E) k else 0 :=
    ae_all_iff.mpr (fun k => raceInteriorBernoulli_probability w α k)
  filter_upwards [hall] with E hE
  rw [FiniteAdaptedBernoulli.integral_predictableMeasure _ _ _ g.continuous.measurable]
  unfold interiorCompensatorSum
  apply Finset.sum_congr rfl
  intro k _
  rw [hE k]
  have hloc : projIcc 0 1 zero_le_one (((k.val : ℝ) + 1) / n) = section3Location n k := by
    exact projIcc_of_mem zero_le_one (section3Location n k).property
  dsimp only
  rw [hloc]
  split_ifs <;> ring

/-- Both hypotheses of the Section 2 criterion are proved for the actual
interior row. No conditional-mean or small-maximum assumption remains. -/
theorem section3_predictable_tests
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    ConvergesInProbability (fun n => exponentialRace (w n))
      (fun n E => ∫ y, g y ∂((raceInteriorBernoulli (w n) α).predictableMeasure
        (section3Location n) E : Measure (Icc (0 : ℝ) 1)))
      (∫ y, g y ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1))) := by
  rw [integral_interiorIntensity]
  have h := section3_weighted_compensator w f hnorm hf hα
    (fun x => g (projIcc 0 1 zero_le_one x))
    (g.continuous.comp continuous_projIcc).continuousOn
  have h' := section3_convergence_congr_ae h
    (fun n => raceInteriorBernoulli_integral (w (n + 1)) α g)
  intro ε hε
  exact (tendsto_add_atTop_iff_nat 1).mp (h' ε hε)

theorem section3_predictable_maximum
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ConvergesInProbability (fun n => exponentialRace (w n))
      (fun n => (raceInteriorBernoulli (w n) α).toProcess.rowMaximum n) 0 := by
  intro ε hε
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (section3_max_probability w f hnorm hf hα ε hε)
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa only [ENNReal.toReal_zero] using hlim)
  intro n
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  have hall : ∀ᵐ E ∂exponentialRace (w (n + 1)), ∀ k : Fin (n + 1),
      (raceInteriorBernoulli (w (n + 1)) α).probability k E =
        if ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α then
          predictableChance (w (n + 1)) (raceDraw E) k else 0 :=
    ae_all_iff.mpr (fun k => raceInteriorBernoulli_probability (w (n + 1)) α k)
  filter_upwards [hall] with E hE
  intro hbad
  by_contra hnot
  have hb : ∀ k < n + 1,
      (raceInteriorBernoulli (w (n + 1)) α).toProcess.probability k E < ε := by
    intro k hk
    rw [show (raceInteriorBernoulli (w (n + 1)) α).toProcess.probability k E =
        (raceInteriorBernoulli (w (n + 1)) α).probability ⟨k, hk⟩ E from
      congrFun (FiniteAdaptedBernoulli.toProcess_probability _ ⟨k, hk⟩) E,
      hE ⟨k, hk⟩]
    split_ifs with hsel
    · exact lt_of_not_ge (fun hge => hnot ⟨⟨k, hk⟩, hsel, hge⟩)
    · exact hε
  have hlt := section3_rowMaximum_lt _ (n + 1) E hε hb
  have hnn := (raceInteriorBernoulli (w (n + 1)) α).toProcess.rowMaximum_nonneg (n + 1) E
  change ε < |(raceInteriorBernoulli (w (n + 1)) α).toProcess.rowMaximum (n + 1) E - 0| at hbad
  rw [sub_zero, abs_of_nonneg hnn] at hbad
  exact (not_lt_of_ge hlt.le) hbad

/-- Corollary 3.3, convergence in law of the actual finite point measure.
The limit is constructed as a Poisson count of iid intensity-distributed
locations. Its independent-count PRM characterization is proved separately
in `Section3PoissonLaw`, rather than postulated by a definition. -/
theorem section3_interior_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ E,
      F (interiorFixedPoints α (raceDraw E)) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (interiorIntensity w f hf α hα))) := by
  have h := predictable_poisson_of_integrals
    (fun n => exponentialRace (w n)) (fun n => raceInteriorBernoulli (w n) α)
    section3Location (interiorIntensity w f hf α hα)
    (section3_predictable_tests w f hnorm hf hα)
    (section3_predictable_maximum w f hnorm hf hα) F
  simpa only [raceInteriorBernoulli_pointMeasure] using h

/-- Corollary 3.3 for every Luce permutation model, on arbitrary row
probability spaces. The full masses in `eq:luce-law` are the defining
distribution of the paper's model, not additional asymptotic assumptions. -/
theorem section3_interior_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ)
    {α : ℝ} (hα : α < 1) (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (interiorFixedPoints α (π n ω)) ∂P n) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (interiorIntensity w f hf α hα))) := by
  have heq (n : ℕ) : (∫ ω, F (interiorFixedPoints α (π n ω)) ∂P n) =
      ∫ E, F (interiorFixedPoints α (raceDraw E)) ∂exponentialRace (w n) := by
    letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
    have htest : Measurable (fun σ : Equiv.Perm (Fin n) => F (interiorFixedPoints α σ)) :=
      fun _ _ => trivial
    calc
      _ = ∫ σ, F (interiorFixedPoints α σ) ∂(P n).map (π n) :=
        (integral_map_of_stronglyMeasurable (hπ n) htest.stronglyMeasurable).symm
      _ = ∫ σ, F (interiorFixedPoints α σ) ∂(exponentialRace (w n)).map raceDraw := by
        rw [luce_map_eq_raceDraw (P n) (w n) (π n) (hπ n) (hMass n)]
      _ = _ := integral_map_of_stronglyMeasurable (measurable_raceDraw n) htest.stronglyMeasurable
  simpa only [heq] using section3_interior_poisson w f hnorm hf hα F

end Luce
