import Luce.Section4EndpointIntegrals
import Luce.Section4EndpointCapacityAnalytic

/-! Generic integral assembly. Its early and late premises must be proved
for the actual exponential race; this is not the concrete block theorem. -/
noncomputable section
open MeasureTheory Real Set
open scoped BigOperators
namespace Luce

theorem capacity_integral_bound {ι : Type*} (indices : Finset ι)
    (θ : ι → ℝ) (p : ι → ℝ → ℝ) {γ s q : ℝ}
    (hγ : 0 < γ) (hs : 0 < s) (hq : 0 ≤ q)
    (hθ : ∀ i ∈ indices, γ ≤ θ i)
    (hpmeas : ∀ i ∈ indices, Measurable (p i))
    (hp : ∀ t ∈ Ioi 0, ∀ i ∈ indices, 0 ≤ p i t ∧ p i t ≤ 1)
    (hearly : ∀ t ∈ Ioc 0 s, ∀ i ∈ indices, p i t ≤ q)
    (hlate : ∀ t ∈ Ioi s, (∑ i ∈ indices, θ i * Real.exp (-θ i * t) * p i t) ≤ γ / (Real.exp (γ * t) - 1)) :
    (∑ i ∈ indices, ∫ t : ℝ in Ioi 0, θ i * Real.exp (-θ i * t) * p i t) ≤
      (indices.card : ℝ) * q + endpointQ (γ * s) := by
  have hs0 : 0 ≤ s := hs.le
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
  have hlateBound : (∫ t : ℝ in Ioi s, f t) ≤ endpointQ (γ * s) := by
    rw [← integral_capacity_kernel hγ hs]
    apply integral_mono_ae (hfint.mono_set hlateSubset) (integrable_capacity_kernel hγ hs)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hlate t ht
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

end Luce
