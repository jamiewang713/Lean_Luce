import Luce.Section6InteriorTargetBound
import Luce.Section6InsertionHolder

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal
namespace Luce.Section6

/-- Joint middle-rank cylinders have the required inverse-row product bound.
No separation of demanded ranks, beyond distinctness, is assumed. -/
theorem PowerProfile.interior_rank_cylinder_bound {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r : ℕ) (hr : 0 < r) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (u j : Fin r → Fin n), Injective u → Injective j →
    (∀ a, eps*(n : ℝ) ≤ ((j a).val : ℝ)+1 ∧
      ((j a).val : ℝ)+1 ≤ (1-eps)*(n : ℝ)) →
    exponentialRace (w n) {clocks | MarkedRankCylinder u j clocks} ≤
      (ENNReal.ofReal (C/(n : ℝ)))^r := by
  classical
  obtain ⟨C, N, hC, hN, hb⟩ := hp.interior_insertion_target_bound heps r r hr
  refine ⟨C, max N (((r : ℝ)+1)/eps), hC, hN.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge u j hu hj hbulk
  have hNn := (le_max_left N (((r : ℝ)+1)/eps)).trans hlarge
  have hrn : (r : ℝ)+1 ≤ eps*(n : ℝ) := by
    have hh := (div_le_iff₀ heps).mp ((le_max_right N (((r : ℝ)+1)/eps)).trans hlarge)
    nlinarith
  let removed := Finset.univ.image (u ∘ Tuple.sort j)
  have hcard : removed.card = r := by
    dsimp [removed]
    rw [Finset.card_image_of_injective _ (hu.comp (Tuple.sort j).injective)]
    simp
  have hcomp : (Finset.univ \ removed).card = n-r := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard]
  have hfactor (a : Fin r) :
      eLpNorm (fun old => (deletedGapKernel (w n) removed old
        ((u ∘ Tuple.sort j) a) (sortedMarkedGapIndex j a)).toReal)
        (r : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C/(n : ℝ)) := by
    have hba := hbulk (Tuple.sort j a)
    have hadd := sortedMarkedGapIndex_add j hj a
    have hvalR : ((j (Tuple.sort j a)).val : ℝ)+(r : ℝ)+1 ≤ n := by nlinarith [hba.2]
    have hval : (j (Tuple.sort j a)).val+r+1 ≤ n := by exact_mod_cast hvalR
    have hq : sortedMarkedGapIndex j a < (Finset.univ \ removed).card := by
      rw [hcomp]
      omega
    have hshift : Nat.dist (sortedMarkedGapIndex j a) ((j (Tuple.sort j a)).val+1-1) ≤ r+1 := by
      have := a.isLt
      unfold Nat.dist
      omega
    have hh := hb grid w hw n ((j (Tuple.sort j a)).val+1) hn hNn
      (by exact_mod_cast hba.1) (by exact_mod_cast hba.2) removed (by omega)
      ((u ∘ Tuple.sort j) a) ⟨sortedMarkedGapIndex j a, hq⟩ r hshift hr (le_refl r)
    exact hh
  apply (markedRankCylinder_probability_le_Lp_product (w n) hr u j hu hj).trans
  calc
    _ ≤ ∏ _a : Fin r, ENNReal.ofReal (C/(n : ℝ)) :=
      Finset.prod_le_prod' (fun a _ => hfactor a)
    _ = _ := by simp

end Luce.Section6
