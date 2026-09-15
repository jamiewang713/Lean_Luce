import Luce.Section5MarkedGapBridge
import Luce.Section5Reservoir

/-!
# The uniform reservoir bound for every deleted elimination order

Source: `fixed_points.tex:1017–1024`. The set removed before gap q consists
of the marked deletions and the q earlier unmarked labels. Its cardinality
is bounded explicitly. No order-dependent rate lower bound is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped BigOperators Topology

namespace Luce
attribute [local instance] Classical.propDecidable

/-- Deleted labels together with the q labels preceding a compact rank. -/
def deletedPrefixLabels {n : ℕ} (removed : Finset (Fin n))
    (σ : Equiv.Perm (Fin (Finset.univ \ removed).card))
    (q : Fin (Finset.univ \ removed).card) : Finset (Fin n) :=
  removed ∪ (Finset.Iio q).image (fun k => deletedClockLabel removed (σ k))

lemma deletedPrefixLabels_card_le {n : ℕ} (removed : Finset (Fin n))
    (σ : Equiv.Perm (Fin (Finset.univ \ removed).card))
    (q : Fin (Finset.univ \ removed).card) :
    (deletedPrefixLabels removed σ q).card ≤ removed.card + q.val := by
  calc
    _ ≤ removed.card + ((Finset.Iio q).image (fun k => deletedClockLabel removed (σ k))).card :=
      Finset.card_union_le _ _
    _ ≤ removed.card + (Finset.Iio q).card := Nat.add_le_add_left (Finset.card_image_le) _
    _ = _ := by rw [Fin.card_Iio]

/-- Complementing the deleted prefix leaves exactly the ordered suffix,
with each original unmarked label counted once. -/
theorem total_compl_deletedPrefixLabels {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (σ : Equiv.Perm (Fin (Finset.univ \ removed).card))
    (q : Fin (Finset.univ \ removed).card) :
    (∑ i ∈ Finset.univ \ deletedPrefixLabels removed σ q, w.rate i) =
      orderedRemainingRate (compactDeletedWeights w removed) σ q := by
  let p := (Finset.Iio q).image (fun k => deletedClockLabel removed (σ k))
  have hf : Injective (fun k => deletedClockLabel removed (σ k)) :=
    (deletedClockLabel_injective removed).comp σ.injective
  have hmem (k) : deletedClockLabel removed (σ k) ∈ p ↔ k < q := by
    simp only [p, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨j, hj, h⟩
      exact hf h ▸ hj
    · intro hk
      exact ⟨k, hk, rfl⟩
  have hset : Finset.univ \ deletedPrefixLabels removed σ q =
      (Finset.univ \ removed).filter (fun i => i ∉ p) := by
    ext i
    simp only [deletedPrefixLabels, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, not_or, Finset.mem_filter, p]
  rw [hset, Finset.sum_filter, ← sum_deletedClockLabel removed
    (fun i => if i ∉ p then w.rate i else 0),
    ← Equiv.sum_comp σ (fun k => if deletedClockLabel removed k ∉ p then
      w.rate (deletedClockLabel removed k) else 0)]
  simp only [hmem, not_lt, orderedRemainingRate, Finset.sum_filter, compactDeletedWeights]

/-- Every compact elimination order has the same deterministic bulk lower
bound. The constant depends only on the fixed profile and α, not the marked
labels, their rates, q, the elimination order, or the row once it is large. -/
theorem ProfileLimit.deleted_suffix_rate_uniform_lower {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop,
      ∀ removed : Finset (Fin n), removed.card ≤ r →
        ∀ q : Fin (Finset.univ \ removed).card, (q.val : ℝ) ≤ α * n →
          ∀ σ : Equiv.Perm (Fin (Finset.univ \ removed).card),
            b * n ≤ orderedRemainingRate (compactDeletedWeights (w n) removed) σ q := by
  obtain ⟨d, η, hd, hη, _, hrem⟩ := hf.moderate_reservoir_with_remaining_rate hα
  refine ⟨d * η, mul_pos hd hη, ?_⟩
  filter_upwards [hrem r] with n hn
  intro removed hr q hq σ
  have hcard : ((deletedPrefixLabels removed σ q).card : ℝ) ≤ α * n + r := by
    have hh : ((deletedPrefixLabels removed σ q).card : ℝ) ≤
        (removed.card : ℝ) + (q.val : ℝ) := by
      exact_mod_cast deletedPrefixLabels_card_le removed σ q
    have hr' : (removed.card : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  rw [← total_compl_deletedPrefixLabels (w n) removed σ q]
  exact hn (deletedPrefixLabels removed σ q) hcard

end Luce
