import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! # Compact approximation through a moment map

These helpers apply to the moment image of finite counting measures. They
use only the stated induced topology, compactness, and algebra separation;
no separation or countability assumption is imposed on the original space.
-/

open Topology
open Filter
open scoped BoundedContinuousFunction

namespace Luce

/-- A continuous real function is constant on the fibers of a map inducing
the topology. The original space need not be Hausdorff or even `T₀`. -/
lemma continuous_factorsThrough_of_isInducing
    {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]
    (J : S → M) (hJ : IsInducing J) (F : C(S, ℝ)) :
    Function.FactorsThrough F J := by
  intro x y hxy
  have hsame : Inseparable (J x) (J y) := by rw [hxy]
  exact ((hJ.inseparable_iff.mp hsame).map F.continuous).eq

/-- Stone-Weierstrass after descending through a surjective moment map.
The compactness of the image is derived from the source. -/
theorem exists_algebra_approximation_of_isInducing
    {S M : Type*} [TopologicalSpace S] [CompactSpace S] [TopologicalSpace M]
    (J : S → M) (hJ : IsInducing J) (hsurj : Function.Surjective J)
    (A : Subalgebra ℝ C(M, ℝ)) (hA : A.SeparatesPoints)
    (F : C(S, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ A, ∀ s : S, ‖a (J s) - F s‖ < ε := by
  let JC : C(S, M) := ⟨J, hJ.continuous⟩
  have hquot : IsQuotientMap JC := hJ.isQuotientMap_of_surjective hsurj
  have hfac : Function.FactorsThrough F JC :=
    continuous_factorsThrough_of_isInducing J hJ F
  let FM : C(M, ℝ) := hquot.lift F hfac
  have hFM (s : S) : FM (J s) = F s :=
    congrArg (fun a : C(S, ℝ) => a s) (hquot.lift_comp F hfac)
  let : CompactSpace M := Function.Surjective.compactSpace hJ.continuous hsurj
  obtain ⟨a, ha⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      A hA FM FM.continuous ε hε
  refine ⟨a, a.property, fun s => ?_⟩
  simpa only [hFM s] using ha (J s)

/-- Approximate a bounded continuous state functional uniformly on a compact
set by an algebra on its moment image. All algebra membership is retained
on the full image space, so the result can be used for Laplace polynomials.
-/
theorem exists_algebra_approximation_on_compact_of_isInducing
    {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]
    (J : S → M) (hJ : IsInducing J)
    (A : Subalgebra ℝ C(M, ℝ)) (hA : A.SeparatesPoints)
    (F : S →ᵇ ℝ) {K : Set S} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ A, ∀ s ∈ K, ‖a (J s) - F s‖ < ε := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let q : K → (J '' K) := fun s => ⟨J s.val, ⟨s.val, s.property, rfl⟩⟩
  have hq : IsInducing q := by
    apply IsInducing.subtypeVal.of_comp_iff.mp
    exact hJ.comp IsInducing.subtypeVal
  have hsurj : Function.Surjective q := by
    rintro ⟨y, s, hs, hsy⟩
    exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
  let restrict : C(M, ℝ) →⋆ₐ[ℝ] C(J '' K, ℝ) :=
    ContinuousMap.compStarAlgHom' ℝ ℝ ⟨Subtype.val, continuous_subtype_val⟩
  let B : Subalgebra ℝ C(J '' K, ℝ) := A.map restrict
  have hB : B.SeparatesPoints := by
    intro x y hxy
    obtain ⟨_, ⟨a, ha, rfl⟩, hne⟩ := hA (Subtype.coe_ne_coe.mpr hxy)
    refine ⟨restrict a, ⟨restrict a, ?_, rfl⟩, hne⟩
    exact Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
  let FK : C(K, ℝ) := F.toContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨b, hb, hbapprox⟩ :=
    exists_algebra_approximation_of_isInducing q hq hsurj B hB FK hε
  obtain ⟨a, ha, hab⟩ := Subalgebra.mem_map.mp hb
  refine ⟨a, ha, fun s hs => ?_⟩
  have h := hbapprox ⟨s, hs⟩
  rw [← hab] at h
  exact h

/-- If the moment algebra is measurable and the state space is exhausted
eventually by compact sets, every bounded continuous real state functional
is measurable. The measurable space is arbitrary: no measurability of all
weak-open sets is needed. -/
theorem measurable_boundedContinuousFunction_of_compact_exhaustion
    {S M : Type*} [TopologicalSpace S] [MeasurableSpace S] [TopologicalSpace M]
    (J : S → M) (hJ : IsInducing J)
    (A : Subalgebra ℝ C(M, ℝ)) (hA : A.SeparatesPoints)
    (hAmeas : ∀ a ∈ A, Measurable (fun s => a (J s)))
    (K : ℕ → Set S) (hK : ∀ n, IsCompact (K n))
    (hcover : ∀ s, ∀ᶠ n in atTop, s ∈ K n) (F : S →ᵇ ℝ) :
    Measurable F := by
  obtain ⟨u, -, hupos, hu⟩ :
      ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  choose a ha happrox using fun n =>
    exists_algebra_approximation_on_compact_of_isInducing J hJ A hA F (hK n) (hupos n)
  apply measurable_of_tendsto_metrizable (fun n => hAmeas (a n) (ha n))
  apply tendsto_pi_nhds.mpr
  intro s
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hu
  filter_upwards [hcover s] with n hn
  simpa only [dist_eq_norm] using (happrox n s hn).le

end Luce
