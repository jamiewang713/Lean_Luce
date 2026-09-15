import Luce.Section4EndpointBlockCapacity
import Luce.Section4EndpointTheorem
import Luce.Section4EndpointShells

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators
namespace Luce

/-- The sum of fixed-point probabilities in a block is its actual expected
number of fixed labels. No integrability input is necessary for a finite count. -/
theorem block_fixedPoint_expectation_eq {n : ℕ} (w : Weights n) (block : Finset (Fin n)) :
    (∫ e, ((block.filter fun i => raceRank e i = i.val + 1).card : ℝ) ∂exponentialRace w) =
      ∑ i ∈ block, (exponentialRace w).real {e | raceRank e i = i.val + 1} := by
  classical
  have hint (i : Fin n) : Integrable
      (fun e => if raceRank e i = i.val + 1 then (1 : ℝ) else 0) (exponentialRace w) := by
    convert! (integrable_const (μ := exponentialRace w) (1 : ℝ)).indicator
        ((measurable_raceRank i) (measurableSet_singleton (i.val + 1))) using 1
    funext e
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  apply Finset.sum_congr rfl
  intro i _
  convert! (integral_indicator_const (μ := exponentialRace w) (1 : ℝ)
      ((measurable_raceRank i) (measurableSet_singleton (i.val + 1)))) using 1
  · apply integral_congr_ae
    filter_upwards [] with e
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
  · simp only [smul_eq_mul, mul_one]
    congr 1

/-- Literal finite minimum and maximum specialization of block capacity.
The extra local quantities in `exponentialRace_block_capacity` are constructed
here, rather than assumed of the weight array. -/
theorem block_endpoint_capacity {n : ℕ} (w : Weights (n + 1))
    (block : Finset (Fin (n + 1))) (hb : block.Nonempty) (s : ℝ) (hs : 0 < s)
    (hcut : (((block.image terminalDepth).max' (hb.image _)) : ℝ) <
      meanSurvivors w.rate s - 1) :
    (∫ e, ((block.filter fun i => raceRank e i = i.val + 1).card : ℝ) ∂exponentialRace w) ≤
      (block.card : ℝ) * Real.exp (-((meanSurvivors w.rate s - 1 -
        (((block.image terminalDepth).max' (hb.image _)) : ℝ)) ^ 2 /
          (2 * (meanSurvivors w.rate s - 1)))) +
        endpointQ (((block.image w.rate).min' (hb.image _)) * s) := by
  rw [block_fixedPoint_expectation_eq]
  apply exponentialRace_block_capacity w block (s := s) _ (Nat.cast_nonneg _) hs _ _ hcut
  · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (Finset.min'_mem (block.image w.rate) (hb.image _))
    rw [← heq]
    exact w.positive i
  · intro i hi
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · intro i hi
    have h := Finset.le_max' (block.image terminalDepth) (terminalDepth i)
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hd : n - i.val ≤ terminalDepth i := by unfold terminalDepth; omega
    exact_mod_cast hd.trans h

end Luce
