import Luce.Section5Microscopic
import Luce.Section5MicroscopicSort
import Luce.Section5CyclicReduction
import Luce.Section5BulkCylinderAll

/-!
# Lemma 5.2: the cyclic local limit

Source: `fixed_points.tex:996–1076`. This entry point assembles the proof
from the original normalization and profile hypotheses. In particular,
the microscopic estimate is proved here from the actual race; it is not
an extra hypothesis of either final theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

namespace Luce

/-- Equation `eq:bounded-marked-asymptotic`, uniformly over arbitrary
distinct marked labels and distinct, macroscopically separated bulk ranks. -/
theorem section5_bounded_marked_asymptotic
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a, (w n).rate (i a) ≤ M) →
        (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
        (∀ a b, a ≠ b → ζ * n ≤ |((j a).val : ℝ) - (j b).val|) →
        |(n : ℝ) ^ r * (exponentialRace (w n)).real
            {old | ∀ a, raceRank old (i a) = (j a).val + 1} -
          ∏ a, finiteCyclicDensity (w n) f (i a) (j a)| < ε :=
  bounded_marked_asymptotic_of_sorted w f r hα M
    (section5_sorted_marked_asymptotic w f hnorm hf r hα M hM)

/-- Equation `eq:cyclic-local-limit` on the literal closed cube with
Lebesgue measure. The test may be signed and is only required continuous
on that cube. The statement includes every α<1, including α≤0. -/
theorem section5_cyclic_local
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) (hr : 0 < r)
    (α : ℝ) (hα : α < 1) (τ : Equiv.Perm (Fin r))
    (g : (Fin r → ℝ) → ℝ) (hg : ContinuousOn g (cyclicBulkCube r α)) :
    Tendsto (fun n => cyclicRaceSum (w n) α τ g) atTop
      (𝓝 (∫ x in cyclicBulkCube r α,
        g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a)))) := by
  have h := hf.cyclic_local_of_bounded_marked_asymptotic hr hα τ hg
    (fun M hM => section5_bounded_marked_asymptotic w f hnorm hf r hα M hM.le)
  rw [cyclicProfileIntegral_eq_volume f hα τ g] at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

/-- The whole of Lemma 5.2: cyclic convergence and its uniform weighted
bulk cylinder bound, with all mathematical assumptions visible. -/
theorem section5_lemma52
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) (hr : 0 < r)
    (α : ℝ) (hα : α < 1) (τ : Equiv.Perm (Fin r))
    (g : (Fin r → ℝ) → ℝ) (hg : ContinuousOn g (cyclicBulkCube r α)) :
    Tendsto (fun n => cyclicRaceSum (w n) α τ g) atTop
      (𝓝 (∫ x in cyclicBulkCube r α,
        g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a)))) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
        ∀ i j : Fin r ↪ Fin n,
          (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
            (exponentialRace (w n)).real
              {old | ∀ a, raceRank old (i a) = (j a).val + 1} ≤
                K / (n : ℝ) ^ r * ∏ a, (w n).rate (i a) :=
  ⟨section5_cyclic_local w f hnorm hf r hr α hα τ g hg,
    hf.weighted_bulk_cylinder_all r hα⟩

end Luce
