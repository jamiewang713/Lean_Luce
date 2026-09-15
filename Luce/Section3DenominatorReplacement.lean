import Luce.Section3Probability
import Luce.Section3Replacement

/-! # Denominator replacement for the full interior sum

This is equation `eq:p-first-approx`, `fixed_points.tex:751–758`.
The estimate uses the actual normalized total weight and does not bound the
number of surviving labels by an assumed asymptotic expression.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal

namespace Luce

theorem race_probability_formula {n : ℕ} (w : Weights n)
    (E : Fin n → ℝ) (hinj : Function.Injective E) (k : Fin n) :
    predictableChance w (raceDraw E) k =
      w.rate k * survivalGe (orderTime E k) (E k) / w.total (remaining (raceDraw E) k) := by
  rw [raceDraw_eq E hinj, predictableChance_formula,
    orderTime_eq_arrivalTime E hinj]
  have hsurv := rank_survives_iff E hinj k k
  change k ≤ (drawPermutation E hinj).symm k ↔ _ at hsurv
  simp only [hsurv, survivalGe, mul_ite, mul_one, mul_zero]

/-- Finite signed-coefficient version of the reciprocal-denominator bound. -/
theorem weighted_denominator_error_le {ι : Type*} (s : Finset ι)
    (a c W D : ι → ℝ) {d δ C : ℝ}
    (hd : 0 < d) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hmass : ∑ i ∈ s, a i ≤ 1)
    (hc : ∀ i ∈ s, |c i| ≤ C)
    (hW : ∀ i ∈ s, d ≤ W i) (hD : ∀ i ∈ s, d ≤ D i)
    (herr : ∀ i ∈ s, |W i - D i| ≤ δ) :
    |(∑ i ∈ s, c i * (a i / W i)) - (∑ i ∈ s, c i * (a i / D i))| ≤
      C * δ / d^2 := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, |c i * (a i / W i) - c i * (a i / D i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (C * δ / d^2) * a i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul]
      have h := abs_div_sub_div_le (ha i hi) hd (hD i hi) (hW i hi) (herr i hi)
      calc
        _ ≤ C * (a i * δ / d^2) :=
          mul_le_mul (hc i hi) h (abs_nonneg _) hC
        _ = _ := by ring
    _ = (C * δ / d^2) * ∑ i ∈ s, a i := by rw [Finset.mul_sum]
    _ ≤ C * δ / d^2 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmass (show 0 ≤ C * δ / d^2 by positivity)

/-- The actual surviving normalized rates have total mass at most one. -/
theorem normalized_surviving_mass_le (w : WeightArray) (hnorm : NormalizedWeights w)
    (n : ℕ) (s : Finset (Fin (n + 1))) (E τ : Fin (n + 1) → ℝ) :
    ∑ i ∈ s, ((w (n + 1)).rate i * survivalGe (τ i) (E i)) / (n + 1 : ℕ) ≤ 1 := by
  have hsum : ∑ i : Fin (n + 1), (w (n + 1)).rate i = ((n + 1 : ℕ) : ℝ) := by
    have h := hnorm (n + 1) (Nat.succ_pos n)
    have hdiv : (∑ i, (w (n + 1)).rate i) / ((n + 1 : ℕ) : ℝ) = 1 := by
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h
    simpa only [one_mul] using (div_eq_iff (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)).mp hdiv
  rw [← Finset.sum_div]
  apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
  calc
    _ ≤ ∑ i ∈ s, (w (n + 1)).rate i := Finset.sum_le_sum fun i _ => by
      have h := (survivalGe_mem_Icc (τ i) (E i)).2
      nlinarith [(w (n + 1)).positive i]
    _ ≤ ∑ i : Fin (n + 1), (w (n + 1)).rate i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i _ _ => ((w (n + 1)).positive i).le)
    _ = _ := hsum

/-- Equation `eq:p-first-approx` for arbitrary uniformly bounded signed
coefficients on the interior labels. All random-denominator control is
proved from normalization and the original profile assumption. -/
theorem denominator_replacement_converges
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (s : ∀ n, Finset (Fin (n + 1)))
    (hs : ∀ n i, i ∈ s n → ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α)
    (g : ∀ n, Fin (n + 1) → ℝ) {G : ℝ}
    (hG : 0 ≤ G) (hg : ∀ n i, i ∈ s n → |g n i| ≤ G) :
    ConvergesInProbability (fun n => exponentialRace (w (n + 1)))
      (fun n E => (∑ i ∈ s n, g n i * predictableChance (w (n + 1)) (raceDraw E) i) -
        (∑ i ∈ s n,
          (g n i / profileD profileMeasure f
            (profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ)))) *
          (w (n + 1)).rate i * survivalGe (orderTime E i) (E i)) / (n + 1 : ℕ)) 0 := by
  intro ε hε
  by_cases hα0 : 0 ≤ α
  · let d := profileD profileMeasure f (profileQuantile profileMeasure f α)
    have hd : 0 < d := (section3_denominator_lower hf hα0 hα).1
    let K := G / (d / 2)^2
    obtain ⟨δ₀, hδ₀, hδsmall⟩ := exists_pos_mul_lt hε K
    let δ := min δ₀ (d/2)
    have hδ : 0 < δ := lt_min hδ₀ (half_pos hd)
    have hK : 0 ≤ K := div_nonneg hG (sq_nonneg _)
    have hsmall : K * δ < ε :=
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hK).trans_lt hδsmall
    have hprob := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp
      (section3_uniform_denominator w f hnorm hf hα δ hδ)
    simp only [Function.comp_def, ENNReal.toReal_zero] at hprob
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hprob
    intro n
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [exponentialRace_injective_ae (w (n + 1))] with E hinj
    intro hbad
    by_contra hgood
    let D (i : Fin (n + 1)) := profileD profileMeasure f
      (profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ)))
    let W (i : Fin (n + 1)) := (w (n + 1)).total (remaining (raceDraw E) i) / (n + 1 : ℕ)
    let a (i : Fin (n + 1)) :=
      (w (n + 1)).rate i * survivalGe (orderTime E i) (E i) / (n + 1 : ℕ)
    have hD (i : Fin (n + 1)) (hi : i ∈ s n) : d ≤ D i :=
      (section3_denominator_lower hf hα0 hα).2 _ ⟨by positivity, hs n i hi⟩
    have herr (i : Fin (n + 1)) (hi : i ∈ s n) : |W i - D i| ≤ δ := by
      have h : |empiricalRemainingGe (w (n + 1)) E (orderTime E i) - D i| < δ :=
        lt_of_not_ge fun he => hgood ⟨i, hs n i hi, he⟩
      simpa only [W, remaining_weight_eq_empirical _ E hinj i] using h.le
    have hW (i : Fin (n + 1)) (hi : i ∈ s n) : d/2 ≤ W i :=
      denominator_lower_bound (hD i hi) ((herr i hi).trans (min_le_right _ _))
    have hbound := weighted_denominator_error_le (s n) a (g n) W D
      (half_pos hd) hδ.le hG
      (fun i _ => div_nonneg (mul_nonneg ((w (n + 1)).positive i).le
        (survivalGe_mem_Icc _ _).1) (by positivity))
      (normalized_surviving_mass_le w hnorm n (s n) E (orderTime E))
      (hg n) hW (fun i hi => (by linarith : d/2 ≤ d).trans (hD i hi)) herr
    have hleft : (∑ i ∈ s n, g n i * (a i / W i)) =
        ∑ i ∈ s n, g n i * predictableChance (w (n + 1)) (raceDraw E) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [race_probability_formula _ E hinj i]
      dsimp [a, W]
      rw [div_div_div_cancel_right₀ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)]
    have hright : (∑ i ∈ s n, g n i * (a i / D i)) =
        (∑ i ∈ s n, (g n i / D i) * (w (n + 1)).rate i *
          survivalGe (orderTime E i) (E i)) / (n + 1 : ℕ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [a]
      ring
    rw [hleft, hright] at hbound
    have halg : G * δ / (d/2)^2 = K * δ := by dsimp [K]; ring
    rw [halg] at hbound
    simp only [sub_zero] at hbad
    exact (not_lt_of_ge (hbound.trans hsmall.le)) hbad
  · have hempty (n : ℕ) : s n = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hα0 ((by positivity : 0 ≤ ((i.val : ℝ) + 1) / (n + 1 : ℕ)).trans (hs n i hi))
    simp only [hempty, Finset.sum_empty, zero_div, sub_zero, abs_zero,
      show ¬ ε < 0 from not_lt.mpr hε.le, Set.ofPred_false, measureReal_empty]
    exact tendsto_const_nhds

end Luce
