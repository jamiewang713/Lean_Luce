import Luce.Section6ExceptionalSums
import Luce.Section6DominationMatrixFixedRight

noncomputable section
namespace Luce.Section6

/-- Reducing the positive decay parameters gives a valid common envelope
on positive integer depths. This is used to reconcile matrix clauses. -/
theorem depth_decay_mono {a d D nu Nu : ℝ} (ha : 1 ≤ a)
    (hd : 0 ≤ d) (hdD : d ≤ D) (hnu : nu ≤ Nu) :
    Real.exp (-D*a^Nu) ≤ Real.exp (-d*a^nu) := by
  apply Real.exp_le_exp.mpr
  have hp : a^nu ≤ a^Nu := Real.rpow_le_rpow_of_exponent_le ha hnu
  have hm := mul_le_mul hp hdD hd (Real.rpow_nonneg (zero_le_one.trans ha) Nu)
  nlinarith

theorem exceptional_envelope_mono_decay {b v d D nu Nu : ℝ} {a h : ℕ}
    (ha : 1 ≤ a) (hd : 0 ≤ d) (hdD : d ≤ D) (hnu : nu ≤ Nu) :
    exceptionalEnvelope b v D Nu a h ≤ exceptionalEnvelope b v d nu a h := by
  unfold exceptionalEnvelope
  split_ifs
  · exact le_rfl
  · exact depth_decay_mono (by exact_mod_cast ha) hd hdD hnu

/-- The fixed-right matrix bound gives the manuscript's outside-corner
decay for any positive cutoff, derived from the same actual matrix. -/
theorem PowerProfile.domination_matrix_fixed_right_outside {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta delta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r H p : ℕ)
    (hp1 : 0 < p) (hdelta : 0 < delta) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i j : Fin n), terminalDepth j ≤ H →
      delta*(n : ℝ) ≤ (terminalDepth i : ℝ) →
      insertionDominationMatrix (w n) r p i j ≤
        C*Real.exp (-d*(n : ℝ)^(beta/(beta+1))) := by
  obtain ⟨C, d, hC, hd, hb⟩ := hp.domination_matrix_fixed_right_decay r H p hp1
  let z := beta/(beta+1)
  have hz : 0 < z := (right_extreme_exponent_bounds hp.2.2.2.1.2.1).1
  refine ⟨C, d*delta^z, hC, mul_pos hd (Real.rpow_pos_of_pos hdelta z), ?_⟩
  intro grid w hw n i j hj hi
  apply (hb grid w hw n i j hj).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have ht := Real.rpow_le_rpow (mul_nonneg hdelta.le (Nat.cast_nonneg n)) hi hz.le
  rw [Real.mul_rpow hdelta.le (Nat.cast_nonneg n)] at ht
  change -(d*delta^z)*(n : ℝ)^z ≥ -d*(terminalDepth i : ℝ)^z
  nlinarith

end Luce.Section6
