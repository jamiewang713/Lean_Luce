import Luce.Section3ProfileKernels

/-! # Continuity of the deterministic race transforms -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Luce

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem continuousOn_profileD {f : Ω → ℝ} (hf : Integrable f μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) : ContinuousOn (profileD μ f) (Ici 0) := by
  apply continuousOn_of_dominated (bound := f)
  · intro t ht
    exact (integrable_rateKernel hf hf₀ ht).aestronglyMeasurable
  · intro t ht
    filter_upwards [hf₀] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (rateKernel_nonneg hx)] using rateKernel_le ht hx
  · exact hf
  · apply Eventually.of_forall
    intro x
    exact (by unfold rateKernel survivalKernel; fun_prop :
      Continuous (fun t => rateKernel t (f x))).continuousOn

theorem continuousOn_profileH [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ContinuousOn (profileH μ f) (Ici 0) := by
  apply continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
  · intro t ht
    exact (integrable_survivalKernel hf hf₀ ht).aestronglyMeasurable
  · intro t ht
    filter_upwards [hf₀] with x hx
    simpa only [Real.norm_eq_abs, abs_of_pos (survivalKernel_pos t (f x))] using
      survivalKernel_le_one ht hx
  · exact integrable_const _
  · apply Eventually.of_forall
    intro x
    exact (by unfold survivalKernel; fun_prop :
      Continuous (fun t => survivalKernel t (f x))).continuousOn

theorem continuousOn_profileF [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ContinuousOn (profileF μ f) (Ici 0) :=
  continuousOn_const.sub (continuousOn_profileH hf hf₀)

theorem antitoneOn_profileD {f : Ω → ℝ} (hf : Integrable f μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) : AntitoneOn (profileD μ f) (Ici 0) := by
  intro s hs t ht hst
  apply integral_mono_ae (integrable_rateKernel hf hf₀ ht) (integrable_rateKernel hf hf₀ hs)
  filter_upwards [hf₀] with x hx
  exact rateKernel_antitone_time hx hst

theorem monotoneOn_profileF [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) :
    MonotoneOn (profileF μ f) (Ici 0) := by
  intro s hs t ht hst
  apply sub_le_sub_left
  apply integral_mono_ae (integrable_survivalKernel hf hf₀ ht) (integrable_survivalKernel hf hf₀ hs)
  filter_upwards [hf₀] with x hx
  exact survivalKernel_antitone_time hx hst

end Luce
