import Luce.Section6DominationMatrix
import Luce.Section6InsertionLpEnvelope
import Luce.Section6ExceptionalSums
import Luce.Section6GapOffsets

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The concrete matrix retains the ordinary and exceptional right-corner
envelopes. Only a derived finite target-depth cutoff is excluded. -/
theorem PowerProfile.domination_matrix_right_corner_envelope {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p : ℕ) (hp1 : 0 < p)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    ∃ C d nu H delta : ℝ, 0 < C ∧ 0 < d ∧ 0 < nu ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ i j : Fin n, H ≤ (terminalDepth j : ℝ) →
      (terminalDepth j : ℝ)/(n : ℝ) ≤ delta →
      (terminalDepth i : ℝ)/(n : ℝ) ≤ delta →
      insertionDominationMatrix (w n) r p i j ≤
        C*((((terminalDepth i : ℝ)/(terminalDepth j : ℝ))^beta/(terminalDepth j : ℝ))*
          Real.exp (-d*((terminalDepth i : ℝ)/(terminalDepth j : ℝ))^beta)+
          exceptionalEnvelope beta v d nu (terminalDepth i) (terminalDepth j)) := by
  obtain ⟨C, d, nu, H, delta, hC, hd, hnu, hH, hdelta, hdelta1, hb⟩ :=
    hp.right_insertion_Lp_envelope r p hp1 v hv hv1
  refine ⟨C, d, nu, max H (8*(r : ℝ)+8), delta/2, hC, hd, hnu,
    hH.trans_le (le_max_left _ _), half_pos hdelta,
    (half_lt_self hdelta).trans hdelta1, ?_⟩
  intro grid w hw n i j hh hj hi
  have hn : 0 < n := by have := j.isLt; omega
  obtain ⟨removed, q, hremoved, hshift, hval⟩ := insertionDominationMatrix_attained (w n) r p i j
  have hgap : Nat.dist q (n-terminalDepth j) ≤ r+1 := by
    have hjrank : n-terminalDepth j = j.val := by unfold terminalDepth; omega
    rwa [hjrank]
  have hbuffer : 8*r+8 ≤ terminalDepth j := by
    exact_mod_cast (le_max_right H (8*(r : ℝ)+8)).trans hh
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hq : q < (Finset.univ \ removed).card := by
    rw [hcard]
    exact (shifted_right_survivor_bounds hremoved (by unfold terminalDepth; omega) hbuffer hgap).1
  have ht := hb grid w hw n (terminalDepth j) hn ((le_max_left _ _).trans hh)
    (hj.trans_lt (half_lt_self hdelta)) removed hremoved i
    (hi.trans_lt (half_lt_self hdelta)) ⟨q, hq⟩ p hp1 le_rfl hgap
  have hnonneg : 0 ≤ C*((((terminalDepth i : ℝ)/(terminalDepth j : ℝ))^beta/(terminalDepth j : ℝ))*
      Real.exp (-d*((terminalDepth i : ℝ)/(terminalDepth j : ℝ))^beta)+
      exceptionalEnvelope beta v d nu (terminalDepth i) (terminalDepth j)) := by
    have := exceptionalEnvelope_nonneg beta v d nu (terminalDepth i) (terminalDepth j)
    positivity
  apply (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
  rw [hval]
  simpa only [exceptionalEnvelope] using ht

/-- Left-corner matrix envelope, with the manuscript's transposed
exceptional term and a derived finite target-depth cutoff. -/
theorem PowerProfile.domination_matrix_left_corner_envelope {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p : ℕ) (hp1 : 0 < p)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    ∃ C d nu H delta : ℝ, 0 < C ∧ 0 < d ∧ 0 < nu ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ i j : Fin n, H ≤ (j.val : ℝ)+1 →
      ((j.val : ℝ)+1)/(n : ℝ) ≤ delta → ((i.val : ℝ)+1)/(n : ℝ) ≤ delta →
      insertionDominationMatrix (w n) r p i j ≤
        C*(((((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha/((j.val : ℝ)+1))*
          Real.exp (-d*(((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha)+
          exceptionalEnvelope alpha v d nu (j.val+1) (i.val+1)) := by
  obtain ⟨C, d, nu, H, delta, hC, hd, hnu, hH, hdelta, hdelta1, hb⟩ :=
    hp.left_insertion_Lp_envelope r p hp1 v hv hv1
  refine ⟨C, d, nu, max H (8*(r : ℝ)+8), delta/2, hC, hd, hnu,
    hH.trans_le (le_max_left _ _), half_pos hdelta,
    (half_lt_self hdelta).trans hdelta1, ?_⟩
  intro grid w hw n i j hh hj hi
  have hn : 0 < n := by have := j.isLt; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨removed, q, hremoved, hshift, hval⟩ := insertionDominationMatrix_attained (w n) r p i j
  have hgap : Nat.dist q (j.val+1-1) ≤ r+1 := by simpa using hshift
  have hbuffer : 8*r+8 ≤ j.val+1 := by
    exact_mod_cast (le_max_right H (8*(r : ℝ)+8)).trans hh
  have htwice : 2*(j.val+1) ≤ n := by
    have hx : ((j.val : ℝ)+1)/(n : ℝ) ≤ 1/2 := hj.trans (by linarith)
    have hx' := (div_le_iff₀ hnR).mp hx
    have ht : 2*((j.val : ℝ)+1) ≤ n := by linarith
    exact_mod_cast ht
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hq : q < (Finset.univ \ removed).card := by
    rw [hcard]
    exact shifted_left_nonterminal hremoved hbuffer htwice hgap
  have ht := hb grid w hw n (j.val+1) hn
    (by simpa using (le_max_left H _).trans hh)
    (by simpa using hj.trans_lt (half_lt_self hdelta)) removed hremoved i
    (hi.trans_lt (half_lt_self hdelta)) ⟨q, hq⟩ p hp1 le_rfl hgap
  have hnonneg : 0 ≤ C*(((((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha/((j.val : ℝ)+1))*
      Real.exp (-d*(((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha)+
      exceptionalEnvelope alpha v d nu (j.val+1) (i.val+1)) := by
    have := exceptionalEnvelope_nonneg alpha v d nu (j.val+1) (i.val+1)
    positivity
  apply (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
  rw [hval]
  simpa only [exceptionalEnvelope, Nat.cast_add, Nat.cast_one, min_comm] using ht

end Luce.Section6
