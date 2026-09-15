import Luce.Section4EndpointBlockExpectation
import Luce.Section4EndpointShellGeometry
import Luce.Section4EndpointShellEarly
import Luce.Section4EndpointJensen

noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace Luce

theorem shell_survivor_buffer {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j : ℕ) (hs : (terminalShell n j).Nonempty) :
    (shellMax n j hs : ℝ) * Real.exp (Real.sqrt j) ≤
      meanSurvivors (w n).rate ((j : ℝ) - Real.sqrt j) := by
  calc
    _ = ((shellMax n j hs : ℝ) * Real.exp (j : ℝ)) *
        Real.exp (-((j : ℝ) - Real.sqrt j)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (n : ℝ) * Real.exp (-((j : ℝ) - Real.sqrt j)) :=
      mul_le_mul_of_nonneg_right (shellMax_exp_le n j hs) (Real.exp_pos _).le
    _ ≤ _ := hnorm.meanSurvivors_jensen n _

theorem shell_block_expectation_le {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j : ℕ) (hj : 4096 ≤ j) (hb : (terminalShell (n+1) j).Nonempty) :
    (∫ e, (((terminalShell (n+1) j).filter fun i => raceRank e i = i.val+1).card : ℝ)
      ∂exponentialRace (w (n+1))) ≤
      Real.exp (1-Real.sqrt j) +
      endpointQ (shellFloor w (n+1) j hb * ((j : ℝ)-Real.sqrt j)) := by
  have hh : 64 ≤ Real.sqrt (j : ℝ) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 64) (Nat.cast_nonneg j)).mpr
    exact_mod_cast hj
  have hs : 0 < (j : ℝ) - Real.sqrt j := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg j)]
  have hr : (1 : ℝ) ≤ shellMax (n+1) j hb := by
    exact_mod_cast shellMax_pos (n+1) j hb
  have hbuf := shell_survivor_buffer hnorm (n+1) j hb
  have he := Real.add_one_le_exp (Real.sqrt (j : ℝ))
  have hcut : (shellMax (n+1) j hb : ℝ) <
      meanSurvivors (w (n+1)).rate ((j : ℝ)-Real.sqrt j)-1 := by
    nlinarith [mul_nonneg (show 0 ≤ (shellMax (n+1) j hb : ℝ) by linarith)
      (show 0 ≤ Real.exp (Real.sqrt (j : ℝ))-4 by linarith)]
  have hblock := block_endpoint_capacity (w (n+1)) (terminalShell (n+1) j) hb _ hs hcut
  apply hblock.trans
  apply add_le_add _ (le_refl _)
  apply le_trans (mul_le_mul_of_nonneg_right
    (show ((terminalShell (n+1) j).card : ℝ) ≤ shellMax (n+1) j hb by
      exact_mod_cast shell_card_le_max (n+1) j hb) (Real.exp_pos _).le)
  exact shell_early_envelope hr hh (by linarith)

end Luce
