import Luce.Section6DominationMatrixAllWeighted

noncomputable section
namespace Luce.Section6

/-- A common positive exponent is a consequence of the profile, not a new
restriction on models with two active endpoints. -/
theorem PowerProfile.common_weighted_exponent {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right) :
    ∃ kappa : ℝ, 0 < kappa ∧
      (∀ c a e, left = .power c a e → kappa < a) ∧
      (∀ c b e, right = .power c b e → kappa < b) := by
  let L : ℝ := match left with | .finite _ => 1 | .power _ a _ => a
  let R : ℝ := match right with | .finite _ => 1 | .power _ b _ => b
  have hL : 0 < L := by
    cases left with
    | finite c => exact zero_lt_one
    | power c a e => exact zero_lt_one.trans hp.2.2.1.2.1
  have hR : 0 < R := by
    cases right with
    | finite c => exact zero_lt_one
    | power c b e => exact hp.2.2.2.1.2.1
  have hm : 0 < min L R := lt_min hL hR
  refine ⟨min L R / 2, half_pos hm, ?_, ?_⟩
  · intro c a e he
    have h := (half_lt_self hm).trans_le (min_le_left L R)
    subst left
    simpa [L] using h
  · intro c b e he
    have h := (half_lt_self hm).trans_le (min_le_right L R)
    subst right
    simpa [R] using h

/-- Both active weighted rows, with the exponent and the common constant
constructed from the original profile. Inactive endpoints are vacuous. -/
theorem PowerProfile.domination_matrix_common_weighted_rows {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (r p : ℕ) (hp1 : 0 < p) :
    ∃ C kappa : ℝ, 0 < C ∧ 0 < kappa ∧
    (∀ c a e, left = .power c a e →
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (i : Fin n) (s : Finset (Fin n)),
        (∑ j ∈ s, (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa*
          insertionDominationMatrix (w n) r p i j) ≤ C) ∧
    (∀ c b e, right = .power c b e →
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (i : Fin n) (s : Finset (Fin n)),
        (∑ j ∈ s, ((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa*
          insertionDominationMatrix (w n) r p i j) ≤ C) := by
  obtain ⟨k, hk, hkl, hkr⟩ := hp.common_weighted_exponent
  have hl : ∃ C : ℝ, 0 < C ∧ ∀ c a e, left = .power c a e →
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (i : Fin n) (s : Finset (Fin n)),
        (∑ j ∈ s, (((i.val : ℝ)+1)/((j.val : ℝ)+1))^k*
          insertionDominationMatrix (w n) r p i j) ≤ C := by
    cases left with
    | finite c => exact ⟨1, zero_lt_one, by simp⟩
    | power c a e =>
      obtain ⟨C, hC, hb⟩ := hp.domination_matrix_left_weighted_row_all_n hk.le (hkl c a e rfl) r p hp1
      refine ⟨C, hC, ?_⟩
      intro c' a' e' he
      cases he
      exact hb
  have hr : ∃ C : ℝ, 0 < C ∧ ∀ c b e, right = .power c b e →
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (i : Fin n) (s : Finset (Fin n)),
        (∑ j ∈ s, ((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^k*
          insertionDominationMatrix (w n) r p i j) ≤ C := by
    cases right with
    | finite c => exact ⟨1, zero_lt_one, by simp⟩
    | power c b e =>
      obtain ⟨C, hC, hb⟩ := hp.domination_matrix_right_weighted_row_all_n hk.le (hkr c b e rfl) r p hp1
      refine ⟨C, hC, ?_⟩
      intro c' b' e' he
      cases he
      exact hb
  obtain ⟨L, hL, hl⟩ := hl
  obtain ⟨R, hR, hr⟩ := hr
  refine ⟨L+R, k, add_pos hL hR, hk, ?_, ?_⟩
  · intro c a e he grid w hw n i s
    exact (hl c a e he grid w hw n i s).trans (by linarith)
  · intro c b e he grid w hw n i s
    exact (hr c b e he grid w hw n i s).trans (by linarith)

end Luce.Section6
