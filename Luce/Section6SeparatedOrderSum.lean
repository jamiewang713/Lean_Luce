import Luce.Section6DeletedProductTransfer
import Luce.Section6SeparatedInsertion
import Luce.Section6ContractDefinitions

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace Luce.Section6

/-- Either corner block supplies the terminal buffer when its constructed
lower cutoff is at least r+1 and its width is at most one half. -/
theorem endpoint_block_terminal_buffer {n r : ℕ} {delta : ℝ}
    (hd : delta ≤ 1/2) (side : Corner) (j : Fin n)
    (hl : r+1 ≤ cornerDistance side j)
    (hu : (cornerDistance side j : ℝ) ≤ delta*(n : ℝ)) : r < n-j.val := by
  cases side with
  | right => change r+1 ≤ n-j.val at hl; omega
  | left =>
    change r+1 ≤ j.val+1 at hl
    have hlR : (r : ℝ)+1 ≤ (j.val : ℝ)+1 := by exact_mod_cast hl
    have huR : (j.val : ℝ)+1 ≤ delta*(n : ℝ) := by simpa [cornerDistance] using hu
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hreal : (r : ℝ)+(j.val : ℝ) < (n : ℝ) := by nlinarith
    have hnat : r+j.val < n := by exact_mod_cast hreal
    omega

/-- A terminal-depth buffer supplies valid nonfinal background indices;
it is not an assumed gap-law or independence property. -/
theorem sorted_gap_nonfinal_of_terminal_buffer {n s r : ℕ} (hs : s ≤ r)
    (u j : Fin s → Fin n) (hu : Injective u) (hj : Injective j)
    (hbuffer : ∀ e, r < n-(j e).val) :
    ∀ e, sortedMarkedGapIndex j e < (Finset.univ \ Finset.univ.image (u ∘ Tuple.sort j)).card := by
  intro e
  have hcard : (Finset.univ.image (u ∘ Tuple.sort j)).card = s := by
    rw [Finset.card_image_of_injective _ (hu.comp (Tuple.sort j).injective), Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hcard]
  have he := sortedMarkedGapIndex_add j hj e
  have hb := hbuffer (Tuple.sort j e)
  omega

/-- Exact separated-cylinder formula as a finite mixture of normalized
spacing expectations. The terminal buffer guarantees every selected gap
is finite; its endpoint-block discharge is a separate numerical step. -/
theorem separated_cylinder_order_sum {n s r : ℕ} (w : Weights n) (hs : s ≤ r)
    (u j : Fin s → Fin n) (hu : Injective u) (hj : Injective j)
    (hsep : ∀ a b, a ≠ b → 2*r < Nat.dist (j a).val (j b).val)
    (hbuffer : ∀ e, r < n-(j e).val) :
    let removed := Finset.univ.image (u ∘ Tuple.sort j)
    let q : Fin s → Fin (Finset.univ \ removed).card := fun e =>
      ⟨sortedMarkedGapIndex j e, sorted_gap_nonfinal_of_terminal_buffer hs u j hu hj hbuffer e⟩
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} =
      ∑ sigma : Equiv.Perm (Fin (Finset.univ \ removed).card),
        (compactDeletedWeights w removed).mass sigma *
        (∫ xi, ∏ e, exponentialGapMass (w.rate (u (Tuple.sort j e)))
          (gapStartFromNormalized (compactDeletedWeights w removed) sigma (q e) xi)
          (xi (q e)/orderedRemainingRate (compactDeletedWeights w removed) sigma (q e))
          ∂standardGapLaw (Finset.univ \ removed).card) := by
  dsimp only
  rw [separated_cylinder_eq_gap_product w hs u j hu hj hsep]
  simp only [ENNReal.toReal_prod]
  exact deleted_kernel_product_order_sum w _ (u ∘ Tuple.sort j)
    (fun e => ⟨sortedMarkedGapIndex j e, sorted_gap_nonfinal_of_terminal_buffer hs u j hu hj hbuffer e⟩)

end Luce.Section6
