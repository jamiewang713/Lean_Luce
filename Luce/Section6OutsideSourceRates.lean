import Luce.Section6RightRateFloor

noncomputable section
namespace Luce.Section6

/-- Outside a fixed left source block the sampled rates are bounded above,
including when the other endpoint is active. -/
theorem PowerProfile.sampled_upper_outside_left {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ M : ℝ, 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), eps ≤ ((i.val : ℝ)+1)/(n : ℝ) → (w n).rate i ≤ M := by
  obtain ⟨M, hM, hb⟩ := hp.upper_away_left (half_pos heps) (by linarith)
  refine ⟨M, hM, ?_⟩
  intro grid w hw n i hi
  rw [hw n i]
  apply hb _ ⟨?_, (samplePoint_mem grid i).2⟩
  have hs := samplePoint_ge_half_label grid i
  linarith

/-- Outside a fixed right source block the sampled rates are bounded below.
This is derived from the profile, without a global positive rate floor. -/
theorem PowerProfile.sampled_lower_outside_right {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ b : ℝ, 0 < b ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), eps ≤ (terminalDepth i : ℝ)/(n : ℝ) → b ≤ (w n).rate i := by
  obtain ⟨b, hb, hbound⟩ := hp.lower_away_right (half_pos heps) (by linarith)
  refine ⟨b, hb, ?_⟩
  intro grid w hw n i hi
  rw [hw n i]
  apply hbound _ ⟨(samplePoint_mem grid i).1, ?_⟩
  have hs := samplePoint_ge_half_label grid i.rev
  have hdepth : (i.rev.val : ℝ)+1 = (terminalDepth i : ℝ) := by
    exact_mod_cast (show i.rev.val+1 = terminalDepth i by rw [Fin.val_rev]; unfold terminalDepth; omega)
  rw [hdepth, samplePoint_rev] at hs
  linarith

end Luce.Section6
