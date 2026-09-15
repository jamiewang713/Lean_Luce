import Luce.Section6FastWeightedPrototype

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- A scaled weighted prototype bounds the fast perturbation sums. Its
constants are uniform over both grids and all positive rows. -/
theorem scaled_fast_weighted_average_bound {a d : ℝ} (ha : 1 < a) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (grid : SamplingGrid) (n : ℕ), 0 < n →
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      t*((∑ i : Fin n, rateKernel (d*t) ((samplePoint grid n i)^(-a)))/(n : ℝ)) ≤
      K*(t^(1/a)+1/(n : ℝ)) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hga : 0 < 1-1/a := by
    have hh := (one_div_lt_one_div_of_lt zero_lt_one ha)
    rw [div_one] at hh
    linarith
  let A := (Real.Gamma (1-1/a)/a)*d^(1/a-1)
  let B := 2*Real.exp (-1)/d
  let C := 1/(a-1)
  have hA : 0 < A := mul_pos (div_pos (Real.Gamma_pos_of_pos hga) ha0)
    (Real.rpow_pos_of_pos hd _)
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := one_div_pos.mpr (sub_pos.mpr ha)
  refine ⟨A+B+C, by positivity, ?_⟩
  intro grid n hn t ht ht1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp := fast_weighted_prototype_error grid hn ha (c := 1) zero_lt_one (mul_pos hd ht)
  simp only [one_mul, Real.one_rpow, mul_one] at hp
  have hupper := (abs_le.mp hp).2
  have htime : t*(d*t)^(1/a-1) = d^(1/a-1)*t^(1/a) := by
    rw [Real.mul_rpow hd.le ht.le]
    have hh : t*t^(1/a-1) = t^(1/a) := by
      conv_lhs => lhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      ring
    calc
      _ = d^(1/a-1)*(t*t^(1/a-1)) := by ring
      _ = _ := by rw [hh]
  have hsmall : t ≤ t^(1/a) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge ht ht1
      (show 1/a ≤ (1 : ℝ) by linarith)
    simpa only [Real.rpow_one] using hh
  calc
    _ ≤ t*((Real.Gamma (1-1/a)/a)*(d*t)^(1/a-1) +
        (2*(Real.exp (-1)/(d*t)))/(n : ℝ)+1/(a-1)) := by
      apply mul_le_mul_of_nonneg_left _ ht.le
      linarith
    _ = A*t^(1/a)+B/(n : ℝ)+C*t := by
      dsimp [A, B, C]
      have hh : t*((Real.Gamma (1-1/a)/a)*(d*t)^(1/a-1)) =
          (Real.Gamma (1-1/a)/a)*d^(1/a-1)*t^(1/a) := by
        calc
          _ = (Real.Gamma (1-1/a)/a)*(t*(d*t)^(1/a-1)) := by ring
          _ = _ := by rw [htime]; ring
      rw [mul_add, mul_add, hh]
      field_simp
    _ ≤ A*t^(1/a)+B/(n : ℝ)+C*t^(1/a) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsmall hC.le)
    _ ≤ _ := by
      have h1 := mul_nonneg hB.le (Real.rpow_pos_of_pos ht (1/a)).le
      have h2 := mul_nonneg (add_pos hA hC).le (one_div_nonneg.mpr hn0.le)
      simp only [div_eq_mul_inv, one_mul] at *
      nlinarith

/-- A sufficient fast-envelope bound with a positive, unprescribed saving.
On (0,1), its exponential is bounded by the weighted prototype with power
alpha-eta. This weaker error rate suffices for the manuscript's existential
positive exponent; it changes neither the leading term nor any input. -/
theorem fast_power_envelope_average_bound {alpha eta d : ℝ}
    (_ha : 1 < alpha) (he : 0 < eta) (hea : eta < alpha-1) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (grid : SamplingGrid) (n : ℕ), 0 < n →
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      t*((∑ i : Fin n, (samplePoint grid n i)^(-alpha+eta)*
        Real.exp (-((d*t)*(samplePoint grid n i)^(-alpha))))/(n : ℝ)) ≤
      K*(t^(1/(alpha-eta))+1/(n : ℝ)) := by
  obtain ⟨K, hK, hbound⟩ := scaled_fast_weighted_average_bound
    (a := alpha-eta) (by linarith) hd
  refine ⟨K, hK, ?_⟩
  intro grid n hn t ht ht1
  have hterm (i : Fin n) : (samplePoint grid n i)^(-alpha+eta)*
      Real.exp (-((d*t)*(samplePoint grid n i)^(-alpha))) ≤
      rateKernel (d*t) ((samplePoint grid n i)^(-(alpha-eta))) := by
    have hs := samplePoint_mem grid i
    have hh := Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le
      (show -alpha ≤ -(alpha-eta) by linarith)
    rw [show -alpha+eta = -(alpha-eta) by ring, rateKernel, survivalKernel]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hs.1 _).le
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hh (mul_pos hd ht).le
    nlinarith
  calc
    _ ≤ t*((∑ i : Fin n, rateKernel (d*t) ((samplePoint grid n i)^(-(alpha-eta))))/(n : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ => hterm i) (Nat.cast_nonneg n)) ht.le
    _ ≤ _ := hbound grid n hn t ht ht1

end Luce.Section6
