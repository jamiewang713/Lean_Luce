import Luce.Section6DominationMatrixLeftTarget
import Luce.Section6DominationMatrixRightTarget
import Luce.Section6DominationMatrixFixedLeft
import Luce.Section6DominationMatrixFixedRight
import Luce.Section6ContractDefinitions

noncomputable section
namespace Luce.Section6

theorem PowerProfile.active_matrix_target {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (r p : ℕ) (hp1 : 0 < p) (side : Corner) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ((cornerBehavior left right side).active →
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (i j : Fin n), (cornerDistance side j : ℝ)/(n : ℝ) ≤ delta →
        insertionDominationMatrix (w n) r p i j ≤ C/(cornerDistance side j : ℝ)) := by
  cases side with
  | left =>
    cases left with
    | finite c => exact ⟨1, 1/2, by norm_num, by norm_num, by norm_num, by simp [cornerBehavior, EndpointBehavior.active]⟩
    | power c a e =>
      obtain ⟨C, d, hC, hd, hd1, hb⟩ := hp.domination_matrix_left_target r p hp1
      refine ⟨C, d, hC, hd, hd1, fun _ => ?_⟩
      simpa only [cornerDistance, Nat.cast_add, Nat.cast_one] using hb
  | right =>
    cases right with
    | finite c => exact ⟨1, 1/2, by norm_num, by norm_num, by norm_num, by simp [cornerBehavior, EndpointBehavior.active]⟩
    | power c b e =>
      obtain ⟨C, d, hC, hd, hd1, hb⟩ := hp.domination_matrix_right_target r p hp1
      refine ⟨C, d, hC, hd, hd1, fun _ => ?_⟩
      simpa only [cornerDistance, terminalDepth] using hb

theorem PowerProfile.active_matrix_column {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (r p : ℕ) (hp1 : 0 < p) (side : Corner) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ((cornerBehavior left right side).active →
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (j : Fin n), (cornerDistance side j : ℝ)/(n : ℝ) ≤ delta →
      ∀ s : Finset (Fin n), (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C) := by
  cases side with
  | left =>
    cases left with
    | finite c => exact ⟨1, 1/2, by norm_num, by norm_num, by norm_num, by simp [cornerBehavior, EndpointBehavior.active]⟩
    | power c a e =>
      obtain ⟨C, d, hC, hd, hd1, hb⟩ := hp.domination_matrix_left_column r p hp1
      refine ⟨C, d, hC, hd, hd1, fun _ => ?_⟩
      simpa only [cornerDistance, Nat.cast_add, Nat.cast_one] using hb
  | right =>
    cases right with
    | finite c => exact ⟨1, 1/2, by norm_num, by norm_num, by norm_num, by simp [cornerBehavior, EndpointBehavior.active]⟩
    | power c b e =>
      obtain ⟨C, d, hC, hd, hd1, hb⟩ := hp.domination_matrix_right_column r p hp1
      refine ⟨C, d, hC, hd, hd1, fun _ => ?_⟩
      simpa only [cornerDistance, terminalDepth] using hb

/-- One constant and one cutoff serve target maxima and columns at both
active endpoints. Every underlying estimate is proved from the profile. -/
theorem PowerProfile.active_matrix_target_columns {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ side : Corner, (cornerBehavior left right side).active →
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (j : Fin n), (cornerDistance side j : ℝ)/(n : ℝ) ≤ delta →
        (∀ i, insertionDominationMatrix (w n) r p i j ≤ C/(cornerDistance side j : ℝ)) ∧
        (∀ s : Finset (Fin n), (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C) := by
  classical
  choose B D hB hD hD1 hb using hp.active_matrix_target r p hp1
  choose F E hF hE hE1 hf using hp.active_matrix_column r p hp1
  let delta := min (min (D .left) (D .right)) (min (E .left) (E .right))
  have hd : 0 < delta := lt_min (lt_min (hD .left) (hD .right)) (lt_min (hE .left) (hE .right))
  have hdD (side : Corner) : delta ≤ D side := by
    cases side
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
  have hdE (side : Corner) : delta ≤ E side := by
    cases side
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  let C := B .left+B .right+F .left+F .right
  have hc : 0 < C := add_pos (add_pos (add_pos (hB .left) (hB .right)) (hF .left)) (hF .right)
  have hBC (side : Corner) : B side ≤ C := by
    have := hB .left; have := hB .right; have := hF .left; have := hF .right
    cases side <;> dsimp [C] <;> linarith
  have hFC (side : Corner) : F side ≤ C := by
    have := hB .left; have := hB .right; have := hF .left; have := hF .right
    cases side <;> dsimp [C] <;> linarith
  refine ⟨C, delta, hc, hd, (hdD .left).trans_lt (hD1 .left), ?_⟩
  intro side hactive grid w hw n j hj
  constructor
  · intro i
    apply (hb side hactive grid w hw n i j (hj.trans (hdD side))).trans
    exact div_le_div_of_nonneg_right (hBC side) (Nat.cast_nonneg _)
  · intro s
    exact (hf side hactive grid w hw n j (hj.trans (hdE side)) s).trans (hFC side)

end Luce.Section6
