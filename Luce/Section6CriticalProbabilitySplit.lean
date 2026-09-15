import Luce.Section6CriticalBlockErrors

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem critical_probability_reference_error {n A B : ℕ} (w : Weights n) (hAB : A ≤ B) :
    (∑ k ∈ Finset.range n, ∫ e,
      |(raceInteriorBernoulli w 1).toProcess.probability k e-criticalReference n A B k| ∂exponentialRace w) ≤
      (∑ k ∈ criticalBlock n 1 A, ∫ e,
        predictableChance w (raceRankPermutation e).symm k ∂exponentialRace w)+
      (∑ k ∈ criticalBlock n A B, ∫ e,
        |predictableChance w (raceRankPermutation e).symm k-
          1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))| ∂exponentialRace w)+
      ∑ k ∈ criticalBlock n (B+1) n, ∫ e,
        predictableChance w (raceRankPermutation e).symm k ∂exponentialRace w := by
  classical
  let p : Fin n → (Fin n → ℝ) → ℝ := fun k e => predictableChance w (raceRankPermutation e).symm k
  have hi (k : Fin n) : Integrable (p k) (exponentialRace w) :=
    integrable_race_permutation_statistic w (fun π => predictableChance w π.symm k)
  have he (k : Fin n) (r : ℝ) : Integrable (fun e => |p k e-r|) (exponentialRace w) :=
    ((hi k).sub (integrable_const _)).abs
  have hrewrite : (∑ k ∈ Finset.range n, ∫ e,
      |(raceInteriorBernoulli w 1).toProcess.probability k e-criticalReference n A B k| ∂exponentialRace w) =
      ∫ e, ∑ k, |p k e-criticalReference n A B k.val| ∂exponentialRace w := by
    rw [← Fin.sum_univ_eq_sum_range,integral_finsetSum _ (fun k _ => he k _)]
    apply Finset.sum_congr rfl
    intro k _
    rw [FiniteAdaptedBernoulli.toProcess_probability]
    apply integral_congr_ae
    filter_upwards [critical_full_probability w k] with e heq
    rw [heq]
  rw [hrewrite]
  have hmono := integral_mono_ae
    (integrable_finsetSum _ fun k _ => he k (criticalReference n A B k.val))
    (((integrable_finsetSum _ fun k _ => hi k).add
      (integrable_finsetSum _ fun k _ => he k
        (1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))))).add
      (integrable_finsetSum _ fun k _ => hi k))
    (ae_of_all (exponentialRace w) fun e => critical_reference_error_split hAB
      (fun k => p k e) (fun k => w.choice_nonneg _ _))
  simp only [Pi.add_apply] at hmono
  have hiEM : Integrable (fun e => (∑ k ∈ criticalBlock n 1 A, p k e)+
      ∑ k ∈ criticalBlock n A B,
        |p k e-1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))|) (exponentialRace w) :=
    (integrable_finsetSum _ fun k _ => hi k).add (integrable_finsetSum _ fun k _ => he k _)
  rw [integral_add hiEM (integrable_finsetSum _ fun k _ => hi k),
    integral_add (integrable_finsetSum _ fun k _ => hi k) (integrable_finsetSum _ fun k _ => he k _),
    integral_finsetSum (criticalBlock n 1 A) (fun k _ => hi k),
    integral_finsetSum (criticalBlock n A B) (fun k _ => he k _),
    integral_finsetSum (criticalBlock n (B+1) n) (fun k _ => hi k)] at hmono
  exact hmono

end Luce.Section6
