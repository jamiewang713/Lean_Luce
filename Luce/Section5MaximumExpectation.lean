import Luce.Section5MaximumRoot
import Luce.Section5CycleProbability

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section5

/-- The expected number of cycles meeting the tail is the sum of the
actual maximum-root event probabilities. The cutoff is not approximated. -/
theorem tailCycleExpectation_eq_maximum_probability_sum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) _ ⊤ π) (k : ℕ) (α : ℝ) :
    (∫ ω, ((cycleCount (π ω) k - bulkCycleCount (π ω) α k : ℕ) : ℝ) ∂P) =
      ∑ v : Fin n, P.real {ω | v ∈ maximumCycleRoots (π ω) k ∧ α*n < (v.val : ℝ)+1} := by
  classical
  have hset (v : Fin n) :
      MeasurableSet {ω | v ∈ maximumCycleRoots (π ω) k ∧ α*n < (v.val : ℝ)+1} :=
    hπ (show @MeasurableSet (Equiv.Perm (Fin n)) ⊤
      {R | v ∈ maximumCycleRoots R k ∧ α*n < (v.val : ℝ)+1} from trivial)
  have heq (ω : Ω) : ((maximumCycleRoots (π ω) k).filter
      (fun v => α*n < (v.val : ℝ)+1)) =
      Finset.univ.filter (fun v => v ∈ maximumCycleRoots (π ω) k ∧ α*n < (v.val : ℝ)+1) := by
    ext v
    simp
  have hint (v : Fin n) : Integrable (fun ω =>
      if v ∈ maximumCycleRoots (π ω) k ∧ α*n < (v.val : ℝ)+1 then (1 : ℝ) else 0) P := by
    convert! (integrable_const (μ := P) (1 : ℝ)).indicator (hset v) using 1
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  simp_rw [tailCycleCount_eq_maximum_roots, heq]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [integral_finsetSum _ (fun v _ => hint v)]
  apply Finset.sum_congr rfl
  intro v _
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
    integral_indicator_const (μ := P) (1 : ℝ) (hset v)

end Luce.Section5
