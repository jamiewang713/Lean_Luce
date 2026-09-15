import Luce.Section5VertexCount

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Every real statistic of the actual finite race permutation is
integrable. The bound is a constructed finite sum, not a moment input. -/
theorem integrable_race_permutation_statistic {n : ℕ} (w : Weights n)
    (F : Equiv.Perm (Fin n) → ℝ) :
    Integrable (fun e => F (raceRankPermutation e)) (exponentialRace w) := by
  let G := fun f : Fin n → Fin n =>
    if h : Function.Bijective f then F (Equiv.ofBijective f h) else 0
  have heq (e : Fin n → ℝ) : G (raceRankPermutation e : Fin n → Fin n) =
      F (raceRankPermutation e) := by
    dsimp [G]
    rw [dif_pos (raceRankPermutation e).bijective]
    congr 1
    ext i
    rfl
  have hm : Measurable (fun e => F (raceRankPermutation e)) := by
    simpa only [Function.comp_def, heq] using
      (measurable_of_countable G).comp measurable_raceRankPermutation_function
  apply Integrable.of_bound hm.aestronglyMeasurable (∑ R : Equiv.Perm (Fin n), ‖F R‖)
  filter_upwards [] with e
  exact Finset.single_le_sum (fun R _ => norm_nonneg (F R)) (Finset.mem_univ (raceRankPermutation e))

end Luce
