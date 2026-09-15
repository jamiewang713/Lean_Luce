import Luce.Section6SampledPowerExpansion

noncomputable section
namespace Luce.Section6

theorem PowerProfile.left_sampled_rate_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), ((i.val : ℝ)+1)/(n : ℝ) < delta →
      |(w n).rate i/(c*((((i.val : ℝ)+1)/(n : ℝ))^(-alpha)))-1| ≤
        C*((((i.val : ℝ)+1)/(n : ℝ))^eta+1/((i.val : ℝ)+1)) := by
  obtain ⟨C, delta, hC, hd, hd1, hbound⟩ :=
    h.2.2.1.2.2.2.sampled_relative_error h.2.2.1.1 h.2.2.1.2.2.1
  refine ⟨C, delta, hC, hd, hd1, ?_⟩
  intro grid w hw n i hi
  rw [hw n i]
  exact hbound grid n i hi

theorem PowerProfile.right_sampled_rate_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < delta →
      |(w n).rate i/(c*(((terminalDepth i : ℝ)/(n : ℝ))^beta))-1| ≤
        C*(((terminalDepth i : ℝ)/(n : ℝ))^eta+1/(terminalDepth i : ℝ)) := by
  obtain ⟨C, delta, hC, hd, hd1, hbound⟩ :=
    h.2.2.2.1.2.2.2.sampled_relative_error h.2.2.2.1.1 h.2.2.2.1.2.2.1
  refine ⟨C, delta, hC, hd, hd1, ?_⟩
  intro grid w hw n i hi
  have hdepth : (i.rev.val : ℝ)+1 = (terminalDepth i : ℝ) := by
    exact_mod_cast (show i.rev.val+1 = terminalDepth i by rw [Fin.val_rev]; unfold terminalDepth; omega)
  have hh := hbound grid n i.rev (by simpa only [hdepth] using hi)
  have hreflect : 1-samplePoint grid n i.rev = samplePoint grid n i := by
    rw [samplePoint_rev]
    ring
  simpa only [hdepth, hreflect, ← hw n i] using hh

end Luce.Section6
