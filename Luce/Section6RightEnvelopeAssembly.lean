import Luce.Section6CommonDecay
import Luce.Section6DominationMatrixCornerEnvelope

noncomputable section
namespace Luce.Section6

/-- Assemble the right corner envelope and both fixed-target estimates.
The final cutoff can be any smaller positive cutoff, so later intersection
with the left and target/column cutoffs does not strengthen the contract. -/
theorem PowerProfile.domination_matrix_right_envelope_assembly {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p : ℕ) (hp1 : 0 < p)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    ∃ (H : ℕ) (delta0 : ℝ), 1 ≤ H ∧ 0 < delta0 ∧ delta0 < 1 ∧
    ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
    ∃ C d nu : ℝ, 0 < C ∧ 0 < d ∧ 0 < nu ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i j : Fin n),
      (H ≤ terminalDepth j →
        (terminalDepth j : ℝ)/(n : ℝ) ≤ delta →
        (terminalDepth i : ℝ)/(n : ℝ) ≤ delta →
        insertionDominationMatrix (w n) r p i j ≤
          C*((((terminalDepth i : ℝ)/(terminalDepth j : ℝ))^beta/(terminalDepth j : ℝ))*
            Real.exp (-d*((terminalDepth i : ℝ)/(terminalDepth j : ℝ))^beta)+
            exceptionalEnvelope beta v d nu (terminalDepth i) (terminalDepth j))) ∧
      (terminalDepth j ≤ H →
        insertionDominationMatrix (w n) r p i j ≤ C*Real.exp (-d*(terminalDepth i : ℝ)^nu) ∧
        (delta*(n : ℝ) ≤ (terminalDepth i : ℝ) →
          insertionDominationMatrix (w n) r p i j ≤ C*Real.exp (-d*(n : ℝ)^nu))) := by
  obtain ⟨B, D, N, h, delta0, hB, hD, hN, hh, hd0, hd01, henv⟩ :=
    hp.domination_matrix_right_corner_envelope r p hp1 v hv hv1
  let H := max 1 ⌈h⌉₊
  refine ⟨H, delta0, le_max_left _ _, hd0, hd01, ?_⟩
  intro delta hd hdd
  obtain ⟨F, d, nu, hF, hdec, hnu, hdD, hnuN, hfixed⟩ :=
    hp.domination_matrix_fixed_right_common r H p hp1 hd (hdd.trans hd01.le) hD hN
  refine ⟨B+F, d, nu, add_pos hB hF, hdec, hnu, ?_⟩
  intro grid w hw n i j
  have hi : 1 ≤ terminalDepth i := by unfold terminalDepth; omega
  have hj : 0 ≤ (terminalDepth j : ℝ) := Nat.cast_nonneg _
  have hx : 0 ≤ ((terminalDepth i : ℝ)/(terminalDepth j : ℝ))^beta :=
    Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hj) _
  constructor
  · intro hH hjd hid
    have hle : h ≤ (terminalDepth j : ℝ) := by
      apply (Nat.le_ceil h).trans
      exact_mod_cast ((le_max_right 1 ⌈h⌉₊).trans hH)
    have he := henv grid w hw n i j hle (hjd.trans hdd) (hid.trans hdd)
    have hm := add_le_add
      (ordinary_envelope_mono_decay hx hj hdD)
      (exceptional_envelope_mono_decay (b := beta) (v := v) (h := terminalDepth j)
        hi hdec.le hdD hnuN)
    apply he.trans
    apply (mul_le_mul_of_nonneg_left hm hB.le).trans
    apply mul_le_mul_of_nonneg_right (by linarith)
    have := exceptionalEnvelope_nonneg beta v d nu (terminalDepth i) (terminalDepth j)
    positivity
  · intro hH
    obtain ⟨hsource, houtside⟩ := hfixed grid w hw n i j hH
    constructor
    · exact hsource.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
    · intro hloc
      exact (houtside hloc).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

end Luce.Section6
