import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Conditional expectation from finite history fibers

The fiber-sum identity is an auxiliary input, to be established from the
Luce permutation masses. No conditional choice law is assumed here.
-/

open MeasureTheory
open scoped BigOperators

namespace Luce

variable {Ω S T : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] [Fintype S]

/-- Any real function of a measurable finite state is integrable. -/
lemma integrable_finite_state (Z : Ω → S)
    (hZ : @Measurable Ω S mΩ ⊤ Z) (f : S → ℝ) :
    Integrable (fun ω => f (Z ω)) P := by
  classical
  have hset (s : S) : MeasurableSet {ω | Z ω = s} := by
    change MeasurableSet (Z ⁻¹' {s})
    exact hZ trivial
  have hrepr : (fun ω => f (Z ω)) =
      fun ω => ∑ s, {ω | Z ω = s}.indicator (fun _ => f s) ω := by
    funext ω
    simp [Set.indicator, eq_comm]
  rw [hrepr]
  exact integrable_finsetSum _ (fun s _ => (integrable_const (f s)).indicator (hset s))

/-- Integration against a measurable finite state is a weighted finite sum. -/
lemma integral_finite_state (Z : Ω → S)
    (hZ : @Measurable Ω S mΩ ⊤ Z) (f : S → ℝ) :
    (∫ ω, f (Z ω) ∂P) = ∑ s, P.real {ω | Z ω = s} * f s := by
  classical
  have hset (s : S) : MeasurableSet {ω | Z ω = s} := by
    change MeasurableSet (Z ⁻¹' {s})
    exact hZ trivial
  have hrepr : (fun ω => f (Z ω)) =
      fun ω => ∑ s, {ω | Z ω = s}.indicator (fun _ => f s) ω := by
    funext ω
    simp [Set.indicator, eq_comm]
  rw [hrepr, integral_finsetSum _
    (fun s _ => (integrable_const (f s)).indicator (hset s))]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_indicator_const (f s) (hset s), smul_eq_mul]

/-- A finite-fiber integral identity characterizes conditioning on the
history of a finite state. Both finite codomains use their discrete sigma
algebras; the probability space itself is arbitrary. -/
theorem condExp_finite_history [Fintype T] [DecidableEq T]
    (Z : Ω → S) (hZ : @Measurable Ω S mΩ ⊤ Z)
    (H : S → T) (f : S → ℝ) (g : T → ℝ)
    (hfiber : ∀ t : T,
      (∑ s ∈ Finset.univ.filter (fun s => H s = t),
        P.real {ω | Z ω = s} * f s) =
      g t * ∑ s ∈ Finset.univ.filter (fun s => H s = t),
        P.real {ω | Z ω = s}) :
    P[(fun ω => f (Z ω)) |
      MeasurableSpace.comap (fun ω => H (Z ω)) ⊤] =ᵐ[P]
        (fun ω => g (H (Z ω))) := by
  classical
  let : MeasurableSpace S := ⊤
  let : MeasurableSpace T := ⊤
  have hH : Measurable H := fun _ _ => trivial
  have hY : Measurable (fun ω => H (Z ω)) := hH.comp hZ
  have hg : Measurable g := fun _ _ => trivial
  have hgm : Measurable[MeasurableSpace.comap (fun ω => H (Z ω)) ⊤]
      (fun ω => g (H (Z ω))) := hg.comp (comap_measurable _)
  have hgi : Integrable (fun ω => g (H (Z ω))) P :=
    integrable_finite_state Z hZ (fun s => g (H s))
  apply (ae_eq_condExp_of_forall_setIntegral_eq hY.comap_le
    (integrable_finite_state Z hZ f) (fun _ _ _ => hgi.integrableOn) ?_
    hgm.stronglyMeasurable.aestronglyMeasurable).symm
  intro a ha _
  obtain ⟨b, hb, rfl⟩ := MeasurableSpace.measurableSet_comap.mp ha
  have hset : MeasurableSet ((fun ω => H (Z ω)) ⁻¹' b) := hY hb
  have hleft : (∫ ω in (fun ω => H (Z ω)) ⁻¹' b, g (H (Z ω)) ∂P) =
      ∑ s, P.real {ω | Z ω = s} * (if H s ∈ b then g (H s) else 0) := by
    rw [← integral_indicator hset]
    simpa only [Set.indicator, Set.mem_preimage] using
      integral_finite_state Z hZ (fun s => if H s ∈ b then g (H s) else 0)
  have hright : (∫ ω in (fun ω => H (Z ω)) ⁻¹' b, f (Z ω) ∂P) =
      ∑ s, P.real {ω | Z ω = s} * (if H s ∈ b then f s else 0) := by
    rw [← integral_indicator hset]
    simpa only [Set.indicator, Set.mem_preimage] using
      integral_finite_state Z hZ (fun s => if H s ∈ b then f s else 0)
  rw [hleft, hright,
    ← Finset.sum_fiberwise Finset.univ H
      (fun s => P.real {ω | Z ω = s} * (if H s ∈ b then g (H s) else 0)),
    ← Finset.sum_fiberwise Finset.univ H
      (fun s => P.real {ω | Z ω = s} * (if H s ∈ b then f s else 0))]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t ∈ b
  · calc
      _ = ∑ s ∈ Finset.univ.filter (fun s => H s = t),
          P.real {ω | Z ω = s} * g t := by
        apply Finset.sum_congr rfl
        intro s hs
        simp only [(Finset.mem_filter.mp hs).2, if_pos ht]
      _ = g t * ∑ s ∈ Finset.univ.filter (fun s => H s = t),
          P.real {ω | Z ω = s} := by rw [← Finset.sum_mul, mul_comm]
      _ = ∑ s ∈ Finset.univ.filter (fun s => H s = t),
          P.real {ω | Z ω = s} * f s := (hfiber t).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        simp only [(Finset.mem_filter.mp hs).2, if_pos ht]
  · have hzero (v : S → ℝ) :
        (∑ s ∈ Finset.univ.filter (fun s => H s = t),
          P.real {ω | Z ω = s} * (if H s ∈ b then v s else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      simp only [(Finset.mem_filter.mp hs).2, if_neg ht, mul_zero]
    rw [hzero (fun s => g (H s)), hzero f]

/-- A version of the finite-history criterion whose candidate is given on
states, is constant on history fibers, and is checked only at represented
histories. No assumption that every history is represented is needed. -/
theorem condExp_finite_history_of_representatives [Fintype T] [DecidableEq T]
    (Z : Ω → S) (hZ : @Measurable Ω S mΩ ⊤ Z)
    (H : S → T) (f r : S → ℝ)
    (hconst : ∀ s₁ s₂, H s₁ = H s₂ → r s₁ = r s₂)
    (hfiber : ∀ s : S,
      (∑ u ∈ Finset.univ.filter (fun u => H u = H s),
        P.real {ω | Z ω = u} * f u) =
      r s * ∑ u ∈ Finset.univ.filter (fun u => H u = H s),
        P.real {ω | Z ω = u}) :
    P[(fun ω => f (Z ω)) |
      MeasurableSpace.comap (fun ω => H (Z ω)) ⊤] =ᵐ[P]
        (fun ω => r (Z ω)) := by
  classical
  let g : T → ℝ := fun t => if h : ∃ s, H s = t then r h.choose else 0
  have hg (s : S) : g (H s) = r s := by
    dsimp [g]
    split_ifs with h
    · exact hconst _ _ h.choose_spec
    · exact False.elim (h ⟨s, rfl⟩)
  have hfiber' (t : T) :
      (∑ s ∈ Finset.univ.filter (fun s => H s = t),
        P.real {ω | Z ω = s} * f s) =
      g t * ∑ s ∈ Finset.univ.filter (fun s => H s = t),
        P.real {ω | Z ω = s} := by
    by_cases h : ∃ s, H s = t
    · obtain ⟨s, rfl⟩ := h
      rw [hg]
      exact hfiber s
    · have he : Finset.univ.filter (fun s => H s = t) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro s _ hs
        exact h ⟨s, hs⟩
      simp [he]
  exact (condExp_finite_history Z hZ H f g hfiber').trans
    (ae_of_all _ (fun ω => hg (Z ω)))

end Luce
