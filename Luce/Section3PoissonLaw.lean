import Luce.Section2FinitePoissonLaw
import Luce.Section2CompactLawConvergence
import Mathlib.Probability.HasLaw
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# The disjoint-count characterization of the canonical Poisson law

The intended correspondence is equality of the actual joint count law with
the product of mathlib's scalar Poisson measures.  Laplace uniqueness below
is proved on the discrete natural-number count space using the already
checked compact approximation theorem, rather than assumed as an interface.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators NNReal ENNReal BoundedContinuousFunction

namespace Luce

abbrev NatCountVector (m : ℕ) := Fin m → ℕ

def natCountLaplace (m : ℕ) (t : Fin m → ℝ≥0) : C(NatCountVector m, ℝ) :=
  ⟨fun a => Real.exp (-(∑ i, (t i : ℝ) * (a i : ℝ))), continuous_of_discreteTopology⟩

lemma natCountLaplace_zero (m : ℕ) : natCountLaplace m 0 = 1 := by
  ext a
  simp [natCountLaplace]

lemma natCountLaplace_add (m : ℕ) (t u : Fin m → ℝ≥0) :
    natCountLaplace m (t + u) = natCountLaplace m t * natCountLaplace m u := by
  ext a
  simp [natCountLaplace, add_mul, Finset.sum_add_distrib, Real.exp_add, mul_comm]

def natCountLaplaceMonoid (m : ℕ) : Submonoid C(NatCountVector m, ℝ) where
  carrier := Set.range (natCountLaplace m)
  one_mem' := ⟨0, natCountLaplace_zero m⟩
  mul_mem' := by
    rintro a b ⟨t, rfl⟩ ⟨u, rfl⟩
    exact ⟨t + u, natCountLaplace_add m t u⟩

def natCountLaplaceAlgebra (m : ℕ) : Subalgebra ℝ C(NatCountVector m, ℝ) :=
  Algebra.adjoin ℝ (natCountLaplaceMonoid m : Set C(NatCountVector m, ℝ))

lemma natCountLaplaceAlgebra_eq_span (m : ℕ) :
    (natCountLaplaceAlgebra m).toSubmodule =
      Submodule.span ℝ (Set.range (natCountLaplace m)) := by
  rw [natCountLaplaceAlgebra, Algebra.adjoin_eq_span, Submonoid.closure_eq]
  rfl

lemma natCountLaplaceAlgebra_separatesPoints (m : ℕ) :
    (natCountLaplaceAlgebra m).SeparatesPoints := by
  classical
  intro a b hab
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  let t : Fin m → ℝ≥0 := fun j => if j = i then 1 else 0
  refine ⟨natCountLaplace m t,
    ⟨natCountLaplace m t, Algebra.subset_adjoin ⟨t, rfl⟩, rfl⟩, ?_⟩
  intro h
  have ht (j : Fin m) : (t j : ℝ) = if j = i then 1 else 0 := by
    by_cases hj : j = i <;> simp [t, hj]
  have heval (z : NatCountVector m) : natCountLaplace m t z = Real.exp (-(z i : ℝ)) := by
    change Real.exp (-(∑ j, (t j : ℝ) * (z j : ℝ))) = _
    simp_rw [ht]
    simp
  rw [heval a, heval b] at h
  exact hi (Nat.cast_injective (neg_injective (Real.exp_injective h)))

lemma norm_natCountLaplace_le_one (m : ℕ) (t : Fin m → ℝ≥0) (a : NatCountVector m) :
    ‖natCountLaplace m t a‖ ≤ 1 := by
  change ‖Real.exp (-(∑ i, (t i : ℝ) * (a i : ℝ)))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ => mul_nonneg (t i).coe_nonneg (Nat.cast_nonneg _))

lemma natCountLaplaceAlgebra_bounded (m : ℕ) (a : C(NatCountVector m, ℝ))
    (ha : a ∈ natCountLaplaceAlgebra m) : ∃ C : ℝ, ∀ x, ‖a x‖ ≤ C := by
  have hspan : a ∈ Submodule.span ℝ (Set.range (natCountLaplace m)) := by
    rw [← natCountLaplaceAlgebra_eq_span]
    exact ha
  clear ha
  induction hspan using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨t, rfl⟩ := ha
      exact ⟨1, norm_natCountLaplace_le_one m t⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      exact ⟨A + B, fun x => (norm_add_le (a x) (b x)).trans (add_le_add (hA x) (hB x))⟩
  | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      exact ⟨|c| * A, fun x => by
        simpa only [ContinuousMap.smul_apply, norm_smul, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left (hA x) (abs_nonneg c)⟩

lemma integrable_natCountLaplaceAlgebra (m : ℕ) (μ : Measure (NatCountVector m))
    [IsFiniteMeasure μ] (a : C(NatCountVector m, ℝ)) (ha : a ∈ natCountLaplaceAlgebra m) :
    Integrable a μ := by
  obtain ⟨C, hC⟩ := natCountLaplaceAlgebra_bounded m a ha
  exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
    (Eventually.of_forall hC)

def natCountBox (m N : ℕ) : Set (NatCountVector m) :=
  Set.range (fun a : Fin m → Fin (N + 1) => fun i => (a i).val)

lemma mem_natCountBox (m N : ℕ) (a : NatCountVector m) :
    a ∈ natCountBox m N ↔ ∀ i, a i ≤ N := by
  constructor
  · rintro ⟨b, rfl⟩ i
    exact Nat.le_of_lt_succ (b i).isLt
  · intro ha
    exact ⟨fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, rfl⟩

lemma natCountBox_compact (m N : ℕ) : IsCompact (natCountBox m N) :=
  (Set.finite_range _).isCompact

lemma natCountBox_measurable (m N : ℕ) : MeasurableSet (natCountBox m N) :=
  (Set.to_countable _).measurableSet

lemma natCountBox_eventually (m : ℕ) (a : NatCountVector m) :
    ∀ᶠ N in atTop, a ∈ natCountBox m N := by
  filter_upwards [eventually_ge_atTop (∑ i, a i)] with N hN
  rw [mem_natCountBox]
  intro i
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans hN

lemma natCountBox_tail_tendsto (m : ℕ) (μ : Measure (NatCountVector m))
    [IsFiniteMeasure μ] : Tendsto (fun N => μ.real (natCountBox m N)ᶜ) atTop (𝓝 0) := by
  have hanti : Antitone (fun N => (natCountBox m N)ᶜ) := by
    intro a b hab x hx hxa
    apply hx
    rw [mem_natCountBox] at hxa ⊢
    exact fun i => (hxa i).trans hab
  have hempty : (⋂ N, (natCountBox m N)ᶜ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨N, hN⟩ := (natCountBox_eventually m a).exists
    exact Set.mem_iInter.mp ha N hN
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun N => (natCountBox_measurable m N).compl.nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at h
  simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

lemma integral_natCountAlgebra_eq (m : ℕ) (μ ν : Measure (NatCountVector m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hLaplace : ∀ t : Fin m → ℝ≥0,
      (∫ a, natCountLaplace m t a ∂μ) = ∫ a, natCountLaplace m t a ∂ν)
    (a : C(NatCountVector m, ℝ)) (ha : a ∈ natCountLaplaceAlgebra m) :
    (∫ x, a x ∂μ) = ∫ x, a x ∂ν := by
  have hspan : a ∈ Submodule.span ℝ (Set.range (natCountLaplace m)) := by
    rw [← natCountLaplaceAlgebra_eq_span]
    exact ha
  clear ha
  induction hspan using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨t, rfl⟩ := ha
      exact hLaplace t
  | zero => simp
  | add a b ha hb hia hib =>
      have haA : a ∈ natCountLaplaceAlgebra m := by
        change a ∈ (natCountLaplaceAlgebra m).toSubmodule
        rwa [natCountLaplaceAlgebra_eq_span]
      have hbA : b ∈ natCountLaplaceAlgebra m := by
        change b ∈ (natCountLaplaceAlgebra m).toSubmodule
        rwa [natCountLaplaceAlgebra_eq_span]
      simp only [ContinuousMap.add_apply,
        integral_add (integrable_natCountLaplaceAlgebra m μ a haA)
          (integrable_natCountLaplaceAlgebra m μ b hbA),
        integral_add (integrable_natCountLaplaceAlgebra m ν a haA)
          (integrable_natCountLaplaceAlgebra m ν b hbA), hia, hib]
  | smul c a _ hia =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul, hia]

def natCountSingletonTest (m : ℕ) (a : NatCountVector m) : NatCountVector m →ᵇ ℝ where
  toFun b := if b = a then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  map_bounded' := ⟨1, fun x y => by
    rw [Real.dist_eq]
    split_ifs <;> norm_num⟩

lemma integral_natCountSingletonTest (m : ℕ) (μ : Measure (NatCountVector m))
    (a : NatCountVector m) :
    (∫ b, natCountSingletonTest m a b ∂μ) = μ.real {a} := by
  have heq : (fun b => natCountSingletonTest m a b) = ({a} : Set (NatCountVector m)).indicator
      (fun _ => (1 : ℝ)) := by
    funext b
    simp only [natCountSingletonTest, Set.indicator_apply, Set.mem_singleton_iff,
      BoundedContinuousFunction.coe_mk]
  rw [heq, integral_indicator (measurableSet_singleton a), setIntegral_const]
  simp

/-- Nonnegative multivariate Laplace transforms determine a finite vector
of natural-number counts. The proof uses finite compact boxes and
Stone-Weierstrass, then actual singleton probabilities. -/
theorem natCountLaw_eq_of_laplace (m : ℕ) (μ ν : Measure (NatCountVector m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hLaplace : ∀ t : Fin m → ℝ≥0,
      (∫ a, natCountLaplace m t a ∂μ) = ∫ a, natCountLaplace m t a ∂ν) : μ = ν := by
  have hBC (F : NatCountVector m →ᵇ ℝ) : (∫ x, F x ∂μ) = ∫ x, F x ∂ν := by
    have htight : ∀ ε : ℝ, 0 < ε → ∃ N,
        ν.real (natCountBox m N)ᶜ ≤ ε ∧
          ∀ᶠ _n : ℕ in atTop, μ.real (natCountBox m N)ᶜ ≤ ε := by
      intro ε hε
      have hμ := (natCountBox_tail_tendsto m μ).eventually (gt_mem_nhds hε)
      have hν := (natCountBox_tail_tendsto m ν).eventually (gt_mem_nhds hε)
      obtain ⟨N, hNμ, hNν⟩ := (hμ.and hν).exists
      exact ⟨N, hNν.le, Eventually.of_forall fun _ => hNμ.le⟩
    have hlim := tendsto_integral_boundedContinuousFunction_of_tight_algebra
      (fun _ : ℕ => μ) ν id IsInducing.id (natCountLaplaceAlgebra m)
      (natCountLaplaceAlgebra_separatesPoints m)
      (fun _a _ha => measurable_of_countable _)
      (fun a ha => by simpa only [id_eq, Real.norm_eq_abs] using natCountLaplaceAlgebra_bounded m a ha)
      (fun a ha => by
        simp only [id_eq, integral_natCountAlgebra_eq m μ ν hLaplace a ha]
        exact tendsto_const_nhds)
      (natCountBox m) (natCountBox_compact m) (natCountBox_measurable m)
      (natCountBox_eventually m) htight F
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  apply Measure.ext_of_singleton
  intro a
  have h := hBC (natCountSingletonTest m a)
  rw [integral_natCountSingletonTest, integral_natCountSingletonTest] at h
  exact (measureReal_eq_measureReal_iff (measure_ne_top μ _) (measure_ne_top ν _)).mp h

section Counts

variable {X : Type*} [MeasurableSpace X]

/-- The floor in the existing representation of a count loses no mass:
evaluation on every measurable set is precisely its natural count. -/
theorem FinitePointMeasure.count_coe_eq (ξ : FinitePointMeasure X)
    {A : Set X} (hA : MeasurableSet A) :
    (ξ.count A : ℝ) = (ξ.toFiniteMeasure A : ℝ) := by
  classical
  obtain ⟨r, x, hx⟩ := ξ.property
  have hmass : ((pointMeasureOfFin x : Measure X).real A) =
      ((Finset.univ.filter (fun i : Fin r => x i ∈ A)).card : ℝ) := by
    have h := integral_pointMeasureOfFin x (A.indicator (fun _ => (1 : ℝ)))
      (measurable_const.indicator hA)
    rw [integral_indicator_const _ hA] at h
    simpa only [smul_eq_mul, mul_one, Set.indicator_apply, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul] using h
  have hξ : ξ.toFiniteMeasure = pointMeasureOfFin x := hx.symm
  unfold FinitePointMeasure.count
  rw [hξ, ← FiniteMeasure.measureReal_eq_coe_coeFn, hmass]
  simp

def disjointCountTest (m : ℕ) (A : Fin m → Set X) (t : Fin m → ℝ≥0) (x : X) : ℝ :=
  ∑ i, (A i).indicator (fun _ => (t i : ℝ)) x

lemma measurable_disjointCountTest (m : ℕ) (A : Fin m → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (t : Fin m → ℝ≥0) :
    Measurable (disjointCountTest m A t) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hA i))

omit [MeasurableSpace X] in
lemma disjointCountTest_nonneg (m : ℕ) (A : Fin m → Set X) (t : Fin m → ℝ≥0) (x : X) :
    0 ≤ disjointCountTest m A t x := by
  apply Finset.sum_nonneg
  intro i hi
  exact Set.indicator_nonneg (fun _ _ => (t i).coe_nonneg) x

lemma pointLaplace_disjointCountTest (m : ℕ) (A : Fin m → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (t : Fin m → ℝ≥0) (ξ : FinitePointMeasure X) :
    pointLaplace (disjointCountTest m A t) ξ =
      natCountLaplace m t (fun i => ξ.count (A i)) := by
  change Real.exp (-(∫ x, disjointCountTest m A t x ∂(ξ.toFiniteMeasure : Measure X))) =
    Real.exp (-(∑ i, (t i : ℝ) * (ξ.count (A i) : ℝ)))
  apply congrArg (fun r : ℝ => Real.exp (-r))
  unfold disjointCountTest
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator_const _ (hA i), smul_eq_mul,
      FiniteMeasure.measureReal_eq_coe_coeFn, ← ξ.count_coe_eq (hA i)]
    ring
  · intro i hi
    exact integrable_pointMeasure ξ _ (measurable_const.indicator (hA i))

omit [MeasurableSpace X] in
lemma one_sub_exp_neg_disjointCountTest (m : ℕ) (A : Fin m → Set X)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (t : Fin m → ℝ≥0) (x : X) :
    1 - Real.exp (-disjointCountTest m A t x) =
      ∑ i, (A i).indicator (fun _ => 1 - Real.exp (-(t i : ℝ))) x := by
  classical
  by_cases hex : ∃ i, x ∈ A i
  · obtain ⟨i, hi⟩ := hex
    have hoff (j : Fin m) (hji : j ≠ i) : x ∉ A j := by
      intro hj
      exact Set.disjoint_left.mp (hdisj hji) hj hi
    have hsum : disjointCountTest m A t x = (t i : ℝ) := by
      unfold disjointCountTest
      rw [Finset.sum_eq_single i]
      · exact Set.indicator_of_mem hi _
      · intro j hj hji
        exact Set.indicator_of_notMem (hoff j hji) _
      · simp
    rw [hsum, Finset.sum_eq_single i]
    · exact (Set.indicator_of_mem hi (fun _ => 1 - Real.exp (-(t i : ℝ)))).symm
    · intro j hj hji
      exact Set.indicator_of_notMem (hoff j hji) _
    · simp
  · have hoff (i : Fin m) : x ∉ A i := fun hi => hex ⟨i, hi⟩
    simp [disjointCountTest, hoff]

lemma integral_one_sub_exp_neg_disjointCountTest (ν : FiniteMeasure X)
    (m : ℕ) (A : Fin m → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (t : Fin m → ℝ≥0) :
    (∫ x, 1 - Real.exp (-disjointCountTest m A t x) ∂(ν : Measure X)) =
      ∑ i, (ν (A i) : ℝ) * (1 - Real.exp (-(t i : ℝ))) := by
  simp_rw [one_sub_exp_neg_disjointCountTest m A hdisj t]
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (hA _), smul_eq_mul,
      FiniteMeasure.measureReal_eq_coe_coeFn]
  · intro i hi
    exact (integrable_const _).indicator (hA i)

/-- The actual joint count Laplace transform of the canonical Poisson
construction, including arbitrary measurable disjoint sets of zero mass. -/
theorem integral_countLaplace_finitePoissonLaw (ν : FiniteMeasure X)
    (m : ℕ) (A : Fin m → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (t : Fin m → ℝ≥0) :
    (∫ ξ, natCountLaplace m t (fun i => ξ.count (A i)) ∂finitePoissonLaw ν) =
      Real.exp (-(∑ i, (ν (A i) : ℝ) * (1 - Real.exp (-(t i : ℝ))))) := by
  simp_rw [← pointLaplace_disjointCountTest m A hA t]
  rw [integral_pointLaplace_finitePoissonLaw ν (disjointCountTest m A t)
    (measurable_disjointCountTest m A hA t) (disjointCountTest_nonneg m A t),
    integral_one_sub_exp_neg_disjointCountTest ν m A hA hdisj t]

lemma integral_natCountLaplace_pi_poisson (m : ℕ) (r : Fin m → ℝ≥0) (t : Fin m → ℝ≥0) :
    (∫ a, natCountLaplace m t a ∂Measure.pi (fun i => poissonMeasure (r i))) =
      Real.exp (-(∑ i, (r i : ℝ) * (1 - Real.exp (-(t i : ℝ))))) := by
  have heq (a : NatCountVector m) : natCountLaplace m t a =
      ∏ i, (Real.exp (-(t i : ℝ))) ^ a i := by
    simp only [natCountLaplace, ContinuousMap.coe_mk, ← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [heq]
  rw [integral_fintype_prod_eq_prod]
  have hi (i : Fin m) :
      (∫ k : ℕ, (Real.exp (-(t i : ℝ))) ^ k ∂poissonMeasure (r i)) =
        Real.exp (-(r i : ℝ) * (1 - Real.exp (-(t i : ℝ)))) :=
    integral_pow_poissonMeasure (r i) (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (t i).coe_nonneg))
  simp_rw [hi]
  rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The Poisson-count plus iid-location construction has exactly the
standard Poisson random-measure property: every finite family of disjoint
measurable sets has the product law of the corresponding scalar Poisson
counts. The spatial space need not be nonempty or standard Borel. -/
theorem finitePoissonLaw_count_joint (ν : FiniteMeasure X)
    (m : ℕ) (A : Fin m → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    (finitePoissonLaw ν).map (fun ξ i => ξ.count (A i)) =
      Measure.pi (fun i => poissonMeasure (ν (A i))) := by
  have hmeas : Measurable (fun ξ : FinitePointMeasure X => fun i => ξ.count (A i)) :=
    measurable_pi_lambda _ (fun i => FinitePointMeasure.measurable_count (hA i))
  have : IsProbabilityMeasure ((finitePoissonLaw ν).map (fun ξ i => ξ.count (A i))) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  apply natCountLaw_eq_of_laplace m
  intro t
  rw [integral_map hmeas.aemeasurable (measurable_of_countable _).aestronglyMeasurable,
    integral_countLaplace_finitePoissonLaw ν m A hA hdisj t,
    integral_natCountLaplace_pi_poisson]

end Counts
end Luce
