import Luce.TwoCandidate
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Estimates for the last positions

Deterministic and analytic estimates used in Section 4 of `fixed_points.tex`.
In particular, normalization supplies a reservoir of weights at most two,
and the two-candidate inequality gives the integrable density envelope that
avoids dividing by the remaining total weight.
-/

open scoped BigOperators
open Real Set MeasureTheory

namespace Luce

noncomputable section

/-- Expected number of survivors of independent exponential clocks. -/
def meanSurvivors {n : ℕ} (θ : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, Real.exp (-θ i * t)

theorem meanSurvivors_pos {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (t : ℝ) :
    0 < meanSurvivors θ t := by
  apply Finset.sum_pos
  · intro i hi
    exact Real.exp_pos _
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem meanSurvivors_antitone {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) : Antitone (meanSurvivors θ) := by
  intro t u htu
  apply Finset.sum_le_sum
  intro i hi
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left htu (neg_nonpos.mpr (hθ i)))

/-- Mean-one normalization forces at least half the rates to be at most two. -/
theorem half_rates_le_two {n : ℕ} (θ : Fin n → ℝ) (hθ : ∀ i, 0 ≤ θ i)
    (hsum : ∑ i, θ i = (n : ℝ)) :
    (n : ℝ) / 2 ≤ ((Finset.univ.filter fun i => θ i ≤ 2).card : ℝ) := by
  classical
  let good := Finset.univ.filter fun i => θ i ≤ 2
  let bad := Finset.univ.filter fun i => ¬ θ i ≤ 2
  have hbad : 2 * (bad.card : ℝ) ≤ ∑ i ∈ bad, θ i := by
    calc
      2 * (bad.card : ℝ) = ∑ i ∈ bad, (2 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ i ∈ bad, θ i := by
        apply Finset.sum_le_sum
        intro i hi
        exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
  have hsum_bad : ∑ i ∈ bad, θ i ≤ (n : ℝ) := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
      intro i hi hnot
      exact hθ i)
  have hcard : good.card + bad.card = n := by
    simpa [good, bad] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => θ i ≤ 2))
  have hcardR : (good.card : ℝ) + (bad.card : ℝ) = n := by exact_mod_cast hcard
  change (n : ℝ) / 2 ≤ (good.card : ℝ)
  linarith

/-- The normalization bound `S(t) ≥ (n/2) exp(-2t)` from Section 4. -/
theorem meanSurvivors_lower_bound {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = (n : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    (n : ℝ) / 2 * Real.exp (-2 * t) ≤ meanSurvivors θ t := by
  classical
  let good := Finset.univ.filter fun i => θ i ≤ 2
  calc
    (n : ℝ) / 2 * Real.exp (-2 * t)
      ≤ (good.card : ℝ) * Real.exp (-2 * t) :=
        mul_le_mul_of_nonneg_right (half_rates_le_two θ hθ hsum) (Real.exp_pos _).le
    _ = ∑ i ∈ good, Real.exp (-2 * t) := by simp
    _ ≤ ∑ i ∈ good, Real.exp (-θ i * t) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg (Finset.mem_filter.mp hi).2) ht
    _ ≤ meanSurvivors θ t := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro i hi hnot; exact (Real.exp_pos _).le)

/-- At sufficiently late times all rates above `γ` have density at most
`γ exp(-γ t)`. This is the decreasing-density step of the endpoint proof. -/
theorem exponential_density_le {a γ t : ℝ} (hγ : 0 < γ) (ha : γ ≤ a)
    (ht : 1 ≤ γ * t) :
    a * Real.exp (-a * t) ≤ γ * Real.exp (-γ * t) := by
  have ht0 : 0 ≤ t := by nlinarith
  have h1 : a ≤ γ * (1 + (a - γ) * t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr ht)]
  have h2 : a ≤ γ * Real.exp ((a - γ) * t) :=
    h1.trans (mul_le_mul_of_nonneg_left (by simpa [add_comm] using
      (Real.add_one_le_exp ((a - γ) * t))) hγ.le)
  calc
    a * Real.exp (-a * t) ≤
        γ * Real.exp ((a - γ) * t) * Real.exp (-a * t) :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = γ * Real.exp (-γ * t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Tail mass of an exponential density. -/
theorem integral_exponential_density_Ioi {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (∫ t : ℝ in Ioi s, a * Real.exp (-a * t)) = Real.exp (-a * s) := by
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha)]
  field_simp

theorem integrableOn_exponential_density_Ioi {a : ℝ} (ha : 0 < a) (s : ℝ) :
    IntegrableOn (fun t : ℝ => a * Real.exp (-a * t)) (Ioi s) :=
  (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) s).const_mul a

/-- Converting the mean-survivor cutoff into the power appearing in the
explicit endpoint estimate. -/
theorem cutoff_exponential_le_rpow {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = (n : ℝ))
    {s B γ : ℝ} (hs : 0 ≤ s) (hcut : meanSurvivors θ s = B) (hγ : 0 ≤ γ) :
    Real.exp (-γ * s) ≤ (2 * B / n) ^ (γ / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := meanSurvivors_lower_bound θ hθ hsum hs
  rw [hcut] at hb
  have hbase : Real.exp (-2 * s) ≤ 2 * B / n := by
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  calc
    Real.exp (-γ * s) = Real.exp (-2 * s) ^ (γ / 2) := by
      rw [← Real.exp_mul]
      congr 1
      ring
    _ ≤ (2 * B / n) ^ (γ / 2) :=
      Real.rpow_le_rpow (Real.exp_pos _).le hbase (by positivity)

/-- The deterministic two-candidate inequality, now with exponential
densities as weights. -/
theorem two_candidate_density_bound {α : Type*} [DecidableEq α]
    (survivors : Finset α) (candidate : ℕ → α) (M : ℕ) (θ : α → ℝ)
    {γ t : ℝ} (hγ : 0 < γ) (ht : 1 ≤ γ * t)
    (hθ : ∀ m ∈ Finset.Icc 1 M, γ ≤ θ (candidate m)) :
    (∑ m ∈ Finset.Icc 1 M,
      if (survivors.erase (candidate m)).card = m - 1
      then θ (candidate m) * Real.exp (-θ (candidate m) * t) else 0)
      ≤ 2 * γ * Real.exp (-γ * t) := by
  classical
  let indices := (Finset.Icc 1 M).filter fun m =>
    (survivors.erase (candidate m)).card = m - 1
  have hc : (indices.card : ℝ) ≤ 2 := by
    exact_mod_cast two_candidate_bound_Icc survivors candidate M
  rw [← Finset.sum_filter]
  change (∑ m ∈ indices, θ (candidate m) * Real.exp (-θ (candidate m) * t)) ≤ _
  calc
    _ ≤ ∑ m ∈ indices, γ * Real.exp (-γ * t) := by
      apply Finset.sum_le_sum
      intro m hm
      exact exponential_density_le hγ (hθ m (Finset.mem_filter.mp hm).1) ht
    _ = (indices.card : ℝ) * (γ * Real.exp (-γ * t)) := by simp
    _ ≤ 2 * (γ * Real.exp (-γ * t)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 2 * γ * Real.exp (-γ * t) := by ring

end

end Luce
