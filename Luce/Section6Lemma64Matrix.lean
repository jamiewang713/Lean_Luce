import Luce.Section6Lemma64Contract
import Luce.Section6ActiveEnvelopes
import Luce.Section6ActiveMatrixTargets
import Luce.Section6CommonWeightedRows
import Luce.Section6DominationMatrixInteriorAll
import Luce.Section6DominationMatrixCylinder

noncomputable section
namespace Luce.Section6

/-- The entire independently frozen matrix proposition, with no external
parameters or assumed intermediate estimates. -/
theorem lemma64_matrix : Lemma64Contract.matrix := by
  classical
  intro f left right hp grid w hw r
  let q := r+1
  have hq : 0 < q := Nat.succ_pos r
  obtain ⟨HL, L, dL, nuL, epsL, hHL, hL, hdL, hnuL, heL, heL1, hleft⟩ :=
    hp.active_left_envelope q q hq 1 zero_lt_one le_rfl
  obtain ⟨HR, epsR, hHR, heR, heR1, hright0⟩ :=
    hp.active_right_envelope q q hq 1 zero_lt_one le_rfl
  obtain ⟨T, epsT, hT, heT, heT1, htarget⟩ := hp.active_matrix_target_columns q q hq
  let delta := min epsL (min epsR epsT)
  have hd : 0 < delta := lt_min heL (lt_min heR heT)
  have hdL' : delta ≤ epsL := min_le_left _ _
  have hdR' : delta ≤ epsR := (min_le_right _ _).trans (min_le_left _ _)
  have hdT' : delta ≤ epsT := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨R, dR, nuR, hR, hdR, hnuR, hright⟩ := hright0 delta hd hdR'
  obtain ⟨W, k, hW, hk, hwl, hwr⟩ := hp.domination_matrix_common_weighted_rows q q hq
  obtain ⟨B, hB, hrow⟩ := hp.domination_matrix_row_bound_all_n q q hq
  obtain ⟨I, hI, hinterior⟩ := hp.domination_matrix_interior_target_all_n hd q q hq
  obtain ⟨J, hJ, hcolumn⟩ := hp.domination_matrix_interior_column_all_n hd q q hq
  let C := 1+L+R+T+W+B+I+J
  have hC : 0 < C := by dsimp [C]; linarith
  have h1C : 1 ≤ C := by dsimp [C]; linarith
  have hLC : L ≤ C := by dsimp [C]; linarith
  have hRC : R ≤ C := by dsimp [C]; linarith
  have hTC : T ≤ C := by dsimp [C]; linarith
  have hWC : W ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hIC : I ≤ C := by dsimp [C]; linarith
  have hJC : J ≤ C := by dsimp [C]; linarith
  let M := fun n => insertionDominationMatrix (w n) q q
  let d : Corner → ℝ := fun s => match s with | .left => dL | .right => dR
  let nu : Corner → ℝ := fun s => match s with | .left => nuL | .right => nuR
  let H : Corner → ℕ := fun s => match s with | .left => HL | .right => HR
  refine ⟨M, C, delta, k, 1, d, nu, H, hC, hd, hdL'.trans_lt heL1, hk,
    zero_lt_one, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro side
    cases side
    · exact ⟨hdL, hnuL, hHL⟩
    · exact ⟨hdR, hnuR, hHR⟩
  · intro n i j
    exact insertionDominationMatrix_nonneg (w n) q q i j
  · intro n t ht u j hu hj
    have hb := markedRankCylinder_real_probability_le_domination_matrix (w n)
      (ht.trans (Nat.le_succ r)) u j hu hj
    apply hb.trans
    have hn : 0 ≤ ∏ a, M n (u a) (j a) :=
      Finset.prod_nonneg (fun a _ => insertionDominationMatrix_nonneg (w n) q q _ _)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h1C hn
  · intro n i
    simpa [M] using (hrow grid w hw n i Finset.univ).trans hBC
  · intro n j hl hu
    constructor
    · intro i
      exact (hinterior grid w hw n i j hl hu).trans
        (div_le_div_of_nonneg_right hIC (Nat.cast_nonneg n))
    · simpa [M] using (hcolumn grid w hw n j hl hu Finset.univ).trans hJC
  · intro c a e he
    have ha : (cornerBehavior left right .left).active := by simp [cornerBehavior, he, EndpointBehavior.active]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n j hj
      have hj' : (cornerDistance .left j : ℝ)/(n : ℝ) ≤ epsT := by
        simpa [cornerDistance] using hj.trans hdT'
      obtain ⟨ht, hc⟩ := htarget .left ha grid w hw n j hj'
      constructor
      · intro i
        simpa [cornerDistance] using (ht i).trans
          (div_le_div_of_nonneg_right hTC (Nat.cast_nonneg (cornerDistance .left j)))
      · simpa [M] using (hc Finset.univ).trans hTC
    · intro n i
      simpa [M] using (hwl c a e he grid w hw n i Finset.univ).trans hWC
    · intro n i j hh hi hj
      apply ((hleft c a e he grid w hw n i j).1 hh (hj.trans hdL') (hi.trans hdL')).trans
      apply mul_le_mul_of_nonneg_right hLC
      have := exceptionalEnvelope_nonneg a 1 dL nuL (j.val+1) (i.val+1)
      positivity
    · intro n i j hh
      apply ((hleft c a e he grid w hw n i j).2 hh).trans
      apply mul_le_mul_of_nonneg_right hLC
      exact div_nonneg ((w n).positive i).le (Real.rpow_nonneg (Nat.cast_nonneg n) a)
  · intro c b e he
    have ha : (cornerBehavior left right .right).active := by simp [cornerBehavior, he, EndpointBehavior.active]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n j hj
      obtain ⟨ht, hc⟩ := htarget .right ha grid w hw n j (hj.trans hdT')
      constructor
      · intro i
        exact (ht i).trans (div_le_div_of_nonneg_right hTC (Nat.cast_nonneg _))
      · simpa [M] using (hc Finset.univ).trans hTC
    · intro n i
      simpa [M, cornerDistance, terminalDepth] using
        (hwr c b e he grid w hw n i Finset.univ).trans hWC
    · intro n i j hh hi hj
      apply ((hright c b e he grid w hw n i j).1 hh hj hi).trans
      apply mul_le_mul_of_nonneg_right hRC
      have := exceptionalEnvelope_nonneg b 1 dR nuR (terminalDepth i) (terminalDepth j)
      positivity
    · intro n i j hh
      exact ((hright c b e he grid w hw n i j).2 hh).1.trans
        (mul_le_mul_of_nonneg_right hRC (Real.exp_pos _).le)
    · intro n i j hh hi
      exact (((hright c b e he grid w hw n i j).2 hh).2 hi).trans
        (mul_le_mul_of_nonneg_right hRC (Real.exp_pos _).le)

end Luce.Section6
