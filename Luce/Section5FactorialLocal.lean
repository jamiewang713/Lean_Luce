import Luce.Section5FactorialExpectation
import Luce.Section5Lemma52

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Relabeling block vertices preserves the actual rank cylinder sum. -/
theorem bulk_factorial_expectation_eq_cyclicRaceSum {n r : ℕ} (w : Weights n)
    (L : ℕ) (m : Fin L → ℕ) (α : ℝ) (e : Section5.CycleVertex L m ≃ Fin r) :
    (∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace w) =
    cyclicRaceSum w α (e.symm.trans ((Section5.cycleBlockPermutation L m).trans e))
      (fun _ => 1) / ∏ ell : Fin L, ((ell.val+1 : ℕ) : ℝ)^m ell := by
  rw [bulk_factorial_expectation_eq_rank_sum]
  congr 1
  unfold cyclicRaceSum
  apply Fintype.sum_equiv (e.embeddingCongr (Equiv.refl (Fin n)))
  intro t
  simp only [one_mul]
  have hc : (∀ x, ((t x).val : ℝ)+1 ≤ α*n) ↔
      (∀ a, ((t (e.symm a)).val : ℝ)+1 ≤ α*n) := e.symm.surjective.forall
  have hp : {z | ∀ x, raceRank z (t x) =
      (t (Section5.cycleBlockPermutation L m x)).val+1} =
      {z | ∀ a, raceRank z (t (e.symm a)) =
      (t (Section5.cycleBlockPermutation L m (e.symm a))).val+1} := by
    ext z
    exact e.symm.surjective.forall
  simp only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.trans_apply, Equiv.symm_apply_apply, hc, hp]

/-- Bulk joint factorial moments converge to the literal block cyclic
integral. Factoring this integral into individual cycle intensities is a
separate remaining obligation. The positive-size premise selects a moment,
and is not a restriction on the rate model. -/
theorem bulk_factorial_tendsto_block_integral (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (m : Fin L → ℕ) (r : ℕ) (hr : 0 < r)
    (e : Section5.CycleVertex L m ≃ Fin r) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace (w n)) atTop
      (𝓝 ((∫ x in cyclicBulkCube r α, ∏ a,
        cyclicProfileDensity f (x a)
          (x ((e.symm.trans ((Section5.cycleBlockPermutation L m).trans e)) a))) /
          ∏ ell : Fin L, ((ell.val+1 : ℕ) : ℝ)^m ell)) := by
  simp_rw [bulk_factorial_expectation_eq_cyclicRaceSum (e := e)]
  have h := section5_cyclic_local w f hnorm hf r hr α hα
    (e.symm.trans ((Section5.cycleBlockPermutation L m).trans e))
    (fun _ => 1) continuousOn_const
  simp only [one_mul] at h
  exact h.div_const _

/-- Canonical indexing of the original block vertices; no representation
witness is an input to the resulting moment limit. -/
def factorialBlockPermutation (L : ℕ) (m : Fin L → ℕ) :
    Equiv.Perm (Fin (Fintype.card (Section5.CycleVertex L m))) :=
  (Fintype.equivFin (Section5.CycleVertex L m)).symm.trans
    ((Section5.cycleBlockPermutation L m).trans
      (Fintype.equivFin (Section5.CycleVertex L m)))

theorem bulk_factorial_tendsto_canonical_block_integral
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (m : Fin L → ℕ)
    (hm : 0 < Fintype.card (Section5.CycleVertex L m)) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace (w n)) atTop
      (𝓝 ((∫ x in cyclicBulkCube (Fintype.card (Section5.CycleVertex L m)) α,
        ∏ a, cyclicProfileDensity f (x a) (x (factorialBlockPermutation L m a))) /
          ∏ ell : Fin L, ((ell.val+1 : ℕ) : ℝ)^m ell)) :=
  bulk_factorial_tendsto_block_integral w f hnorm hf L m _ hm
    (Fintype.equivFin (Section5.CycleVertex L m)) α hα

/-- The zero-order joint moment is exactly one in every original row. -/
theorem bulk_factorial_expectation_zero {n : ℕ} (w : Weights n)
    (L : ℕ) (α : ℝ) :
    (∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial 0 : ℝ)
      ∂exponentialRace w) = 1 := by
  simp

end Luce
