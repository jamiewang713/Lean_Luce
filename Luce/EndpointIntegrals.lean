import Luce.Endpoint

/-! # Integrating the endpoint envelopes

These estimates assemble the analytic part of Proposition `prop:endpoint-bound`.
The inputs are the early-time probability bound and the late-time sum bound;
`EndpointProbability` proves their Bernoulli and two-candidate ingredients.
-/

open scoped BigOperators
open Real Set MeasureTheory

namespace Luce

noncomputable section

/-- A sum of candidate densities is bounded by twice the slowest admissible
density when the sum of the candidate probabilities is at most two. -/
theorem probability_weighted_density_bound {ι : Type*} (indices : Finset ι)
    (θ p : ι → ℝ) {γ t : ℝ} (hγ : 0 < γ) (ht : 1 ≤ γ * t)
    (hθ : ∀ i ∈ indices, γ ≤ θ i) (hp : ∀ i ∈ indices, 0 ≤ p i)
    (hsum : ∑ i ∈ indices, p i ≤ 2) :
    (∑ i ∈ indices, θ i * Real.exp (-θ i * t) * p i) ≤
      2 * γ * Real.exp (-γ * t) := by
  calc
    _ ≤ ∑ i ∈ indices, (γ * Real.exp (-γ * t)) * p i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (exponential_density_le hγ (hθ i hi) ht) (hp i hi)
    _ = (γ * Real.exp (-γ * t)) * (∑ i ∈ indices, p i) := by rw [Finset.mul_sum]
    _ ≤ (γ * Real.exp (-γ * t)) * 2 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * γ * Real.exp (-γ * t) := by ring

/-- Integrating the two-candidate envelope gives the exact terminal term
`2 exp(-γ s)` in the paper. -/
theorem probability_weighted_tail_bound {ι : Type*} (indices : Finset ι)
    (θ : ι → ℝ) (p : ι → ℝ → ℝ) {γ s : ℝ} (hγ : 0 < γ)
    (hs : 1 ≤ γ * s) (hθ : ∀ i ∈ indices, γ ≤ θ i)
    (hpmeas : ∀ i ∈ indices, Measurable (p i))
    (hp : ∀ t ∈ Ioi s, ∀ i ∈ indices, 0 ≤ p i t)
    (hsum : ∀ t ∈ Ioi s, ∑ i ∈ indices, p i t ≤ 2) :
    (∫ t : ℝ in Ioi s, ∑ i ∈ indices, θ i * Real.exp (-θ i * t) * p i t)
      ≤ 2 * Real.exp (-γ * s) := by
  let f : ℝ → ℝ := fun t => ∑ i ∈ indices, θ i * Real.exp (-θ i * t) * p i t
  have hfmeas : Measurable f := by
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_id.const_mul (-θ i)).exp.const_mul (θ i)).mul (hpmeas i hi)
  have hfnonneg : ∀ t ∈ Ioi s, 0 ≤ f t := by
    intro t ht
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (hγ.le.trans (hθ i hi)) (Real.exp_pos _).le) (hp t ht i hi)
  have hbound : ∀ t ∈ Ioi s, f t ≤ 2 * (γ * Real.exp (-γ * t)) := by
    intro t ht
    have ht' : 1 ≤ γ * t := hs.trans (mul_le_mul_of_nonneg_left ht.le hγ.le)
    simpa only [f, mul_assoc] using
      probability_weighted_density_bound indices θ (fun i => p i t) hγ ht' hθ (hp t ht) (hsum t ht)
  have henv : IntegrableOn (fun t : ℝ => 2 * (γ * Real.exp (-γ * t))) (Ioi s) :=
    (integrableOn_exponential_density_Ioi hγ s).const_mul 2
  have hfint : IntegrableOn f (Ioi s) := by
    apply henv.mono' hfmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg t ht)]
    exact hbound t ht
  calc
    _ ≤ ∫ t : ℝ in Ioi s, 2 * (γ * Real.exp (-γ * t)) := by
      apply integral_mono_ae hfint henv
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = 2 * Real.exp (-γ * s) := by
      rw [integral_const_mul, integral_exponential_density_Ioi hγ]

/-- Integrability of a probability-weighted exponential density. -/
theorem integrableOn_probability_weighted_density {a s : ℝ} (ha : 0 < a)
    (p : ℝ → ℝ) (hmeas : Measurable p)
    (hp : ∀ t ∈ Ioi s, 0 ≤ p t ∧ p t ≤ 1) :
    IntegrableOn (fun t => a * Real.exp (-a * t) * p t) (Ioi s) := by
  apply (integrableOn_exponential_density_Ioi ha s).mono'
    (((measurable_id.const_mul (-a)).exp.const_mul a).mul hmeas).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hpt := (hp t ht).1
  change ‖a * Real.exp (-a * t) * p t‖ ≤ a * Real.exp (-a * t)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ a * Real.exp (-a * t) * p t)]
  exact mul_le_of_le_one_right (by positivity) (hp t ht).2

/-- Splitting the candidate rank integrals at the survivor cutoff gives the
two terms in the explicit endpoint bound. -/
theorem endpoint_integral_bound {ι : Type*} (indices : Finset ι)
    (θ : ι → ℝ) (p : ι → ℝ → ℝ) {γ s q : ℝ}
    (hγ : 0 < γ) (hs : 1 ≤ γ * s) (hq : 0 ≤ q)
    (hθ : ∀ i ∈ indices, γ ≤ θ i)
    (hpmeas : ∀ i ∈ indices, Measurable (p i))
    (hp : ∀ t ∈ Ioi 0, ∀ i ∈ indices, 0 ≤ p i t ∧ p i t ≤ 1)
    (hearly : ∀ t ∈ Ioc 0 s, ∀ i ∈ indices, p i t ≤ q)
    (hlate : ∀ t ∈ Ioi s, ∑ i ∈ indices, p i t ≤ 2) :
    (∑ i ∈ indices, ∫ t : ℝ in Ioi 0, θ i * Real.exp (-θ i * t) * p i t) ≤
      (indices.card : ℝ) * q + 2 * Real.exp (-γ * s) := by
  have hs0 : 0 ≤ s := by nlinarith
  let f : ℝ → ℝ := fun t => ∑ i ∈ indices, θ i * Real.exp (-θ i * t) * p i t
  let envelope : ℝ → ℝ := fun t => ∑ i ∈ indices, θ i * Real.exp (-θ i * t)
  have hint : ∀ i ∈ indices,
      IntegrableOn (fun t => θ i * Real.exp (-θ i * t) * p i t) (Ioi 0) := by
    intro i hi
    exact integrableOn_probability_weighted_density (hγ.trans_le (hθ i hi))
      (p i) (hpmeas i hi) (fun t ht => hp t ht i hi)
  have hfint : IntegrableOn f (Ioi 0) := integrable_finsetSum _ hint
  have henvint : IntegrableOn envelope (Ioi 0) := by
    apply integrable_finsetSum
    intro i hi
    exact integrableOn_exponential_density_Ioi (hγ.trans_le (hθ i hi)) 0
  have hqenvint : IntegrableOn (fun t => q * envelope t) (Ioi 0) := henvint.const_mul q
  have hearlySubset : Ioc 0 s ⊆ Ioi (0 : ℝ) := fun t ht => ht.1
  have hlateSubset : Ioi s ⊆ Ioi (0 : ℝ) := fun t ht => hs0.trans_lt ht
  have hearlyBound : (∫ t : ℝ in Ioc 0 s, f t) ≤ (indices.card : ℝ) * q := by
    calc
      _ ≤ ∫ t : ℝ in Ioc 0 s, q * envelope t := by
        apply integral_mono_ae (hfint.mono_set hearlySubset)
          (hqenvint.mono_set hearlySubset)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        dsimp [f, envelope]
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ ≤ θ i * Real.exp (-θ i * t) * q :=
            mul_le_mul_of_nonneg_left (hearly t ht i hi) (by
              exact mul_nonneg (hγ.le.trans (hθ i hi)) (Real.exp_pos _).le)
          _ = q * (θ i * Real.exp (-θ i * t)) := by ring
      _ ≤ ∫ t : ℝ in Ioi 0, q * envelope t := by
        apply setIntegral_mono_set hqenvint
        · filter_upwards [] with t
          apply mul_nonneg hq
          apply Finset.sum_nonneg
          intro i hi
          exact mul_nonneg (hγ.le.trans (hθ i hi)) (Real.exp_pos _).le
        · exact Filter.Eventually.of_forall (fun t ht => hearlySubset ht)
      _ = (indices.card : ℝ) * q := by
        rw [integral_const_mul]
        dsimp [envelope]
        rw [integral_finsetSum]
        · have hm : (∑ i ∈ indices, ∫ t : ℝ in Ioi 0, θ i * Real.exp (-θ i * t)) =
              (indices.card : ℝ) := by
            calc
              _ = ∑ i ∈ indices, (1 : ℝ) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [integral_exponential_density_Ioi (hγ.trans_le (hθ i hi))]
                simp
              _ = (indices.card : ℝ) := by simp
          rw [hm, mul_comm]
        · intro i hi
          exact integrableOn_exponential_density_Ioi (hγ.trans_le (hθ i hi)) 0
  have hlateBound : (∫ t : ℝ in Ioi s, f t) ≤ 2 * Real.exp (-γ * s) :=
    probability_weighted_tail_bound indices θ p hγ hs hθ hpmeas
      (fun t ht i hi => (hp t (hlateSubset ht) i hi).1) hlate
  have hunion : Ioc 0 s ∪ Ioi s = Ioi (0 : ℝ) := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact hs0.trans_lt ht
    · intro ht
      by_cases hts : t ≤ s
      · exact Or.inl ⟨ht, hts⟩
      · exact Or.inr (lt_of_not_ge hts)
  have hdisjoint : Disjoint (Ioc (0 : ℝ) s) (Ioi s) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact not_lt_of_ge ht.2 ht'
  rw [← integral_finsetSum _ hint]
  change (∫ t : ℝ in Ioi 0, f t) ≤ _
  rw [← hunion, setIntegral_union hdisjoint measurableSet_Ioi
    (hfint.mono_set hearlySubset) (hfint.mono_set hlateSubset)]
  exact add_le_add hearlyBound hlateBound

end

end Luce
