import Luce.Section6LeftEnvelopeAssembly
import Luce.Section6RightEnvelopeAssembly

noncomputable section
namespace Luce.Section6

/-- Left envelope outputs for every permitted profile, with no restriction
at an inactive endpoint. All estimates are constructed, not assumed. -/
theorem PowerProfile.active_left_envelope {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (r p : ℕ) (hp1 : 0 < p)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    ∃ (H : ℕ) (C d nu delta : ℝ), 1 ≤ H ∧ 0 < C ∧ 0 < d ∧ 0 < nu ∧
      0 < delta ∧ delta < 1 ∧
    ∀ c alpha eta, left = .power c alpha eta →
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i j : Fin n),
      (H ≤ j.val+1 → ((j.val : ℝ)+1)/(n : ℝ) ≤ delta →
        ((i.val : ℝ)+1)/(n : ℝ) ≤ delta →
        insertionDominationMatrix (w n) r p i j ≤
          C*(((((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha/((j.val : ℝ)+1))*
            Real.exp (-d*(((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha)+
            exceptionalEnvelope alpha v d nu (j.val+1) (i.val+1))) ∧
      (j.val+1 ≤ H → insertionDominationMatrix (w n) r p i j ≤
        C*((w n).rate i/(n : ℝ)^alpha)) := by
  cases left with
  | finite c =>
    refine ⟨1, 1, 1, 1, 1/2, by omega, zero_lt_one, zero_lt_one, zero_lt_one,
      by norm_num, by norm_num, ?_⟩
    simp
  | power c a e =>
    obtain ⟨H, C, d, nu, delta, hH, hC, hd, hnu, hdelta, hdelta1, hb⟩ :=
      hp.domination_matrix_left_envelope_assembly r p hp1 v hv hv1
    refine ⟨H, C, d, nu, delta, hH, hC, hd, hnu, hdelta, hdelta1, ?_⟩
    intro c' a' e' he
    cases he
    exact hb

/-- Right envelope outputs preserve the order of choosing the final cutoff
before the shared decay constants, including when the endpoint is inactive. -/
theorem PowerProfile.active_right_envelope {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (r p : ℕ) (hp1 : 0 < p)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    ∃ (H : ℕ) (delta0 : ℝ), 1 ≤ H ∧ 0 < delta0 ∧ delta0 < 1 ∧
    ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
    ∃ C d nu : ℝ, 0 < C ∧ 0 < d ∧ 0 < nu ∧
    ∀ c beta eta, right = .power c beta eta →
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
  cases right with
  | finite c =>
    refine ⟨1, 1/2, by omega, by norm_num, by norm_num, ?_⟩
    intro delta hd hdd
    exact ⟨1, 1, 1, zero_lt_one, zero_lt_one, zero_lt_one, by simp⟩
  | power c b e =>
    obtain ⟨H, delta0, hH, hd0, hd01, hb⟩ :=
      hp.domination_matrix_right_envelope_assembly r p hp1 v hv hv1
    refine ⟨H, delta0, hH, hd0, hd01, ?_⟩
    intro delta hd hdd
    obtain ⟨C, d, nu, hC, hdec, hnu, he⟩ := hb delta hd hdd
    refine ⟨C, d, nu, hC, hdec, hnu, ?_⟩
    intro c' b' e' heq
    cases heq
    exact he

end Luce.Section6
