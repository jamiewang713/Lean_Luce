import Luce.Section3Poisson
import Luce.Section3PoissonLaw
import Luce.Section4Endpoint

/-! # Exact count bridges for the full fixed-point measure

Source: `fixed_points.tex:155–159,930`. The full process reuses the existing
interior process at cutoff one. Clock ranks and draw-permutation fixed points
agree on the proved full-measure event of distinct clocks.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open Classical

namespace Luce

/-- The full process is the existing literal Dirac sum with cutoff one. -/
abbrev fixedPoints {n : ℕ} (π : Equiv.Perm (Fin n)) := interiorFixedPoints 1 π

/-- Evaluation of an observed point measure is the exact selected-label count. -/
theorem observedPointMeasure_count {X : Type*} [MeasurableSpace X] {n : ℕ}
    (x : Fin n → X) (b : Fin n → Bool) {A : Set X} (hA : MeasurableSet A) :
    (observedPointMeasure x b).count A =
      (Finset.univ.filter fun k => b k = true ∧ x k ∈ A).card := by
  classical
  apply Nat.cast_injective (R := ℝ)
  have h := integral_observedPointMeasure x b (A.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hA)
  rw [integral_indicator_const _ hA, smul_eq_mul, mul_one,
    FiniteMeasure.measureReal_eq_coe_coeFn, ← FinitePointMeasure.count_coe_eq _ hA] at h
  rw [h]
  simp only [Finset.card_filter, Nat.cast_sum, Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro k _
  cases b k <;> by_cases hx : x k ∈ A <;> simp [hx]

/-- The inverse of the sorted draw permutation has exactly the clock rank. -/
lemma raceDraw_fixed_iff_rankOf {n : ℕ} (e : Fin n → ℝ)
    (hinj : Function.Injective e) (k : Fin n) :
    (raceDraw e).symm k = k ↔ rankOf e k = k.val + 1 := by
  rw [raceDraw_eq e hinj, rankOf_eq_raceRank_for_tail]
  change clockRank e k = k ↔ 1 + (clockRank e k).val = k.val + 1
  rw [Fin.ext_iff]
  omega

/-- The source's `Ξ_n((α,1])` is exactly the existing spatial tail count.
No rounding or off-by-one error is absorbed in an inequality. -/
theorem fixedPoints_tail_count {n : ℕ} (e : Fin n → ℝ)
    (hinj : Function.Injective e) (α : ℝ) :
    (fixedPoints (raceDraw e)).count {x | α < x.val} = tailFixedPointCount e α := by
  classical
  rw [fixedPoints, interiorFixedPoints, observedPointMeasure_count _ _
    (measurableSet_lt measurable_const measurable_subtype_coe)]
  unfold tailFixedPointCount
  congr 1
  apply Finset.filter_congr
  intro k _
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
  have hloc : ((k.val : ℝ) + 1) / n ≤ 1 := (section3Location n k).property.2
  simp only [decide_eq_true_eq, hloc, true_and, Set.mem_ofPred_eq,
    section3Location, raceDraw_fixed_iff_rankOf e hinj k]
  rw [lt_div_iff₀ hn]
  exact and_comm

/-- The exact process-count bridge holds almost surely under the model's
clock law; distinctness is proved, not supplied as a hypothesis. -/
theorem fixedPoints_tail_count_ae {n : ℕ} (w : Weights n) (α : ℝ) :
    (fun e => (fixedPoints (raceDraw e)).count {x | α < x.val}) =ᵐ[exponentialRace w]
      (fun e => tailFixedPointCount e α) := by
  filter_upwards [exponentialRace_injective_ae w] with e he
  exact fixedPoints_tail_count e he α

/-- Equation `eq:tail-tightness` for evaluation of the actual random finite
point measure, now connected exactly to the previously proved count theorem. -/
theorem section4_point_measure_tail_tightness (w : WeightArray)
    (hnorm : NormalizedWeights w) (hend : EndpointAssumption w) :
    Tendsto (fun α : ℝ => limsup (fun n => (exponentialRace (w n)).real
      {e | 0 < (fixedPoints (raceDraw e)).count {x | α < x.val}}) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have h := tail_fixed_point_tightness (fun n => Fin n → ℝ)
    (fun n => exponentialRace (w n)) w hnorm hend (fun _ i e => e i)
    (fun n i => ⟨(exponentialRace_eval (w n) i).measurable.aemeasurable,
      (exponentialRace_eval (w n) i).map_eq⟩)
    (fun n => exponentialRace_independent (w n))
  have heq (α : ℝ) (n : ℕ) : (exponentialRace (w n)).real
      {e | 0 < (fixedPoints (raceDraw e)).count {x | α < x.val}} =
      (exponentialRace (w n)).real {e | 0 < tailFixedPointCount e α} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [fixedPoints_tail_count_ae (w n) α] with e he
    exact propext (by change (0 < _) ↔ (0 < _); rw [he])
  simpa only [heq] using h

end Luce
