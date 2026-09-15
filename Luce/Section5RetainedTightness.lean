import Luce.Section5RetainedProbabilityBound
import Luce.Section5FiniteShellCosts
import Luce.Section5RetainedLabels

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Retained maximum-cycle tightness with the manuscript's cutoff order.
The source cutoff precedes the fixed interior low-rate cutoff, which
precedes the target cutoff and the eventual row. All finite helper premises
are discharged from normalization, the raw shell condition, and the literal
retained label set. This does not yet count the discarded cycles. -/
theorem EndpointShellAssumption.retained_maximum_tightness {w : WeightArray}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J₀ : ℕ, 2 ≤ J₀ ∧ ∀ M δ : ℝ, 0 < δ →
      ∃ J : ℕ, J₀ ≤ J ∧ ∀ᶠ n : ℕ in atTop,
        (∑ v ∈ deepShellLabels n J, (exponentialRace (w n)).real
          (retainedMaximumCycleEvent (k+1)
            (retainedCycleLabels (w n) M (1 - Real.exp (-(J₀ : ℝ))/2) δ) v)) < ε := by
  let C : ℝ := (2*(k+2)+1 : ℕ)^(k+2)
  have hC : 0 < C := by dsimp [C]; positivity
  have he3 : 0 < ε/3 := by positivity
  have heC : 0 < ε/(3*C) := by positivity
  obtain ⟨Ja, hJa⟩ := earlyCycleShellTail_small hnorm k
    (ε := ENNReal.ofReal (ε/3)) (by positivity)
  obtain ⟨Jb, hJb⟩ := (nonnegativeTail_limit_iff _).mp hend.buffered_exp
    (ENNReal.ofReal (ε/(3*C))) (by positivity)
  obtain ⟨Jf, hJf2, hJf⟩ := hend.eventually_buffered_floor_gt_one
  let J₀ := max Jb Jf
  have hJ₀2 : 2 ≤ J₀ := hJf2.trans (le_max_right _ _)
  refine ⟨J₀, hJ₀2, ?_⟩
  intro M δ hδ
  have hsmall := (tendsto_interior_late_error hδ).eventually (gt_mem_nhds heC)
  obtain ⟨J, hJlarge, hJcut, hJsmall⟩ :=
    ((eventually_ge_atTop (max J₀ Ja)).and
      ((eventually_interior_density_cutoff hδ).and hsmall)).exists
  have hJJ₀ : J₀ ≤ J := (le_max_left _ _).trans hJlarge
  have hJJa : Ja ≤ J := (le_max_right _ _).trans hJlarge
  have hJ1 : 1 ≤ J := (by omega : 1 ≤ J₀).trans hJJ₀
  refine ⟨J, hJJ₀, ?_⟩
  filter_upwards [hJb, hJf, eventually_retained_labels_cover w M δ J₀] with n hnB hnF hnCover
  let S := retainedCycleLabels (w n) M (1 - Real.exp (-(J₀ : ℝ))/2) δ
  let S₀ := retainedInteriorLabels (w n) M (1 - Real.exp (-(J₀ : ℝ))/2) δ
  have hfloor : ∀ r ∈ Finset.Icc J₀ n, ∀ hs : (terminalShell n r).Nonempty,
      1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r) := by
    intro r hr hs
    exact hnF r ((le_max_right Jb Jf).trans (Finset.mem_Icc.mp hr).1) hs
  have hbound := retained_deep_probability_bound w n J₀ J k S S₀ hδ
    (by omega) hJ1 hJcut
    (fun u hu => retainedInteriorLabels_rate (w n) M _ δ hu) hnCover hfloor
  have hEarly :
      (∑ j ∈ Finset.Icc J n, ∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
        earlyGhostKernel (w n) (k+2) old u v ((j : ℝ) - Real.sqrt j) *
          markedReturnWeight (ghostEntry (w n) (k+2) old) k v u ∂exponentialRace (w n)) < ε/3 := by
    apply (ENNReal.ofReal_lt_ofReal_iff he3).mp
    exact (early_finite_shell_sum_le_tail w k n J).trans_lt
      ((nonnegativeTail_antitone _ n hJJa).trans_lt (hJa n))
  have hLate : (∑ r ∈ Finset.Icc J₀ n, if hs : (terminalShell n r).Nonempty then
      Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0) < ε/(3*C) := by
    apply (ENNReal.ofReal_lt_ofReal_iff heC).mp
    exact (buffered_finite_shell_sum_le_tail w n J₀ hJ₀2).trans_lt
      ((nonnegativeTail_antitone _ n (le_max_left Jb Jf)).trans_lt hnB)
  have hInterior : C * Real.exp (-δ*((J : ℝ) - Real.sqrt J)) < ε/3 := by
    have := mul_lt_mul_of_pos_left hJsmall hC
    have hcancel : C * (ε/(3*C)) = ε/3 := by field_simp
    rwa [hcancel] at this
  have hTerminal : C * (∑ r ∈ Finset.Icc J₀ n, if hs : (terminalShell n r).Nonempty then
      Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0) < ε/3 := by
    have := mul_lt_mul_of_pos_left hLate hC
    have hcancel : C * (ε/(3*C)) = ε/3 := by field_simp
    rwa [hcancel] at this
  change (∑ v ∈ deepShellLabels n J,
    (exponentialRace (w n)).real (retainedMaximumCycleEvent (k+1) S v)) < ε
  change _ ≤ _ + C * _ at hbound
  rw [mul_add] at hbound
  linarith

end Luce
