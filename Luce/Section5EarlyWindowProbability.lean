import Luce.Section5EarlyWindowEvent
import Luce.Section5EarlyExponent
import Luce.Section4EndpointCapacityChernoff

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce

/-- A cutoff depending only on the fixed window width absorbs its finite
offset. No restriction on the rate array is hidden in this cutoff. -/
theorem early_ghost_shell_probability {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j ell : ℕ) (hshell : (terminalShell n j).Nonempty)
    (hj : (64 + 2 * (ell + 1)) ^ 2 ≤ j) :
    ((terminalShell n j).card : ℝ) *
      (exponentialRace (w n)).real
        (earlyGhostSurvivorEvent n (shellMax n j hshell) ell
          ((j : ℝ) - Real.sqrt j)) ≤ Real.exp (1 - Real.sqrt j) := by
  have hh : (64 + 2 * (ell + 1) : ℝ) ≤ Real.sqrt (j : ℝ) := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg j)).mpr
    exact_mod_cast hj
  have hell : (0 : ℝ) ≤ ell := Nat.cast_nonneg ell
  have hh64 : 64 ≤ Real.sqrt (j : ℝ) := by linarith
  have ht : 0 ≤ (j : ℝ) - Real.sqrt j := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg j)]
  have hr : (1 : ℝ) ≤ shellMax n j hshell := by
    exact_mod_cast shellMax_pos n j hshell
  have he := Real.add_one_le_exp (Real.sqrt (j : ℝ))
  have hoff : 2 * ((ell : ℝ) + 1) ≤ Real.exp (Real.sqrt (j : ℝ)) := by linarith
  have hhalf : 2 * ((shellMax n j hshell : ℝ) + ell) ≤
      (shellMax n j hshell : ℝ) * Real.exp (Real.sqrt (j : ℝ)) := by
    nlinarith [mul_nonneg (show 0 ≤ (shellMax n j hshell : ℝ) - 1 by linarith)
      (show 0 ≤ Real.exp (Real.sqrt (j : ℝ)) - 2 by linarith)]
  have hcut : (shellMax n j hshell : ℝ) + ell <
      (shellMax n j hshell : ℝ) * Real.exp (Real.sqrt (j : ℝ)) := by
    linarith
  have hmean : (shellMax n j hshell : ℝ) * Real.exp (Real.sqrt (j : ℝ)) ≤
      ∑ i ∈ (Finset.univ : Finset (Fin n)),
        ∫ e, clockSurvivalIndicator ((j : ℝ) - Real.sqrt j) i e
          ∂exponentialRace (w n) := by
    simpa only [integral_clockSurvivalIndicator (w n) _ ht, meanSurvivors] using
      shell_survivor_buffer hnorm n j hshell
  have hp := bernoulli_block_lower_tail (exponentialRace (w n))
    (clockSurvivalIndicator ((j : ℝ) - Real.sqrt j))
    (measurable_clockSurvivalIndicator _) (clockSurvivalIndicator_zero_one _)
    (clockSurvivalIndicator_independent (w n) _) Finset.univ
    (show 0 ≤ (shellMax n j hshell : ℝ) + ell by positivity) hcut hmean
  change (exponentialRace (w n)).real (earlyGhostSurvivorEvent n
    (shellMax n j hshell) ell ((j : ℝ) - Real.sqrt j)) ≤ _ at hp
  calc
    _ ≤ (shellMax n j hshell : ℝ) * Real.exp
        (-(((shellMax n j hshell : ℝ) * Real.exp (Real.sqrt j) -
          ((shellMax n j hshell : ℝ) + ell)) ^ 2 /
          (2 * ((shellMax n j hshell : ℝ) * Real.exp (Real.sqrt j))))) :=
      mul_le_mul (by exact_mod_cast shell_card_le_max n j hshell) hp
        ENNReal.toReal_nonneg (by positivity)
    _ ≤ _ := shell_early_envelope_offset hr (Nat.cast_nonneg ell) hh64 hoff

end Luce
