import Luce.Section6DecayCompatibility

noncomputable section
namespace Luce.Section6

/-- The ordinary corner envelope remains valid when its decay is reduced. -/
theorem ordinary_envelope_mono_decay {x h d D : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h) (hd : d ≤ D) :
    (x/h)*Real.exp (-D*x) ≤ (x/h)*Real.exp (-d*x) := by
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hx hh)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Construct one positive exponent and coefficient for the corner envelope,
fixed-depth bound, and the outside-corner bound at a chosen final cutoff. -/
theorem common_decay_parameters {D E N Z delta : ℝ}
    (hD : 0 < D) (hE : 0 < E) (hN : 0 < N) (hZ : 0 < Z)
    (hd : 0 < delta) (hd1 : delta ≤ 1) :
    ∃ b d nu : ℝ, 0 < b ∧ 0 < d ∧ 0 < nu ∧
      b ≤ D ∧ b ≤ E ∧ d ≤ b ∧ nu ≤ N ∧ nu ≤ Z ∧ d = b*delta^nu := by
  let b := min D E
  let nu := min N Z
  have hb : 0 < b := lt_min hD hE
  have hn : 0 < nu := lt_min hN hZ
  have hp : delta^nu ≤ 1 := by
    simpa using Real.rpow_le_rpow hd.le hd1 hn.le
  refine ⟨b, b*delta^nu, nu, hb,
    mul_pos hb (Real.rpow_pos_of_pos hd nu), hn,
    min_le_left _ _, min_le_right _ _, ?_, min_le_left _ _, min_le_right _ _, rfl⟩
  nlinarith

/-- First lower the exponent at positive source depth, then use its
outside-corner location. No uniform lower bound on endpoint rates is used. -/
theorem outside_depth_decay {a n delta b E nu Z : ℝ}
    (ha : 1 ≤ a) (hn : 0 ≤ n) (hd : 0 ≤ delta)
    (hb : 0 ≤ b) (hbE : b ≤ E) (hnu : 0 ≤ nu) (hnuZ : nu ≤ Z)
    (hloc : delta*n ≤ a) :
    Real.exp (-E*a^Z) ≤ Real.exp (-(b*delta^nu)*n^nu) := by
  apply (depth_decay_mono ha hb hbE hnuZ).trans
  apply Real.exp_le_exp.mpr
  have hp := Real.rpow_le_rpow (mul_nonneg hd hn) hloc hnu
  rw [Real.mul_rpow hd hn] at hp
  nlinarith

/-- The actual fixed-right matrix estimates can share the decay parameters
of any previously constructed envelope. D and N are numerical upper bounds
on the returned parameters, not assumptions about the model or matrix. -/
theorem PowerProfile.domination_matrix_fixed_right_common {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta delta D N : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r H p : ℕ)
    (hp1 : 0 < p) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hD : 0 < D) (hN : 0 < N) :
    ∃ C d nu : ℝ, 0 < C ∧ 0 < d ∧ 0 < nu ∧ d ≤ D ∧ nu ≤ N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i j : Fin n), terminalDepth j ≤ H →
      insertionDominationMatrix (w n) r p i j ≤
        C*Real.exp (-d*(terminalDepth i : ℝ)^nu) ∧
      (delta*(n : ℝ) ≤ (terminalDepth i : ℝ) →
        insertionDominationMatrix (w n) r p i j ≤ C*Real.exp (-d*(n : ℝ)^nu)) := by
  obtain ⟨C, E, hC, hE, hbound⟩ := hp.domination_matrix_fixed_right_decay r H p hp1
  have hZ := (right_extreme_exponent_bounds hp.2.2.2.1.2.1).1
  obtain ⟨b, d, nu, hb, hd, hnu, hbD, hbE, hdb, hnuN, hnuZ, heq⟩ :=
    common_decay_parameters hD hE hN hZ hdelta hdelta1
  refine ⟨C, d, nu, hC, hd, hnu, hdb.trans hbD, hnuN, ?_⟩
  intro grid w hw n i j hj
  have ha : 1 ≤ (terminalDepth i : ℝ) := by
    have hi : 1 ≤ terminalDepth i := by unfold terminalDepth; omega
    exact_mod_cast hi
  have hbase := hbound grid w hw n i j hj
  constructor
  · exact hbase.trans (mul_le_mul_of_nonneg_left
      (depth_decay_mono ha hd.le (hdb.trans hbE) hnuZ) hC.le)
  · intro hloc
    apply hbase.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    rw [heq]
    exact outside_depth_decay ha (Nat.cast_nonneg n) hdelta.le hb.le hbE hnu.le hnuZ hloc

end Luce.Section6
