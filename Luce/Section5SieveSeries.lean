import Luce.Section5SieveRemainder

noncomputable section
open Filter
open scoped BigOperators Topology
namespace Luce

theorem factorial_remainder_tendsto_zero (a : ℝ) (q : ℕ) :
    Tendsto (fun K : ℕ => a ^ (q+(K+1)) /
      ((q.factorial : ℝ) * ((K+1).factorial : ℝ))) atTop (𝓝 0) := by
  have h : Tendsto (fun K : ℕ => a ^ (K+1) / ((K+1).factorial : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (Real.summable_pow_div_factorial a).tendsto_atTop_zero
  have he (K : ℕ) : a ^ (q+(K+1)) / ((q.factorial : ℝ) * ((K+1).factorial : ℝ)) =
      (a^q / (q.factorial : ℝ)) * (a^(K+1) / ((K+1).factorial : ℝ)) := by
    rw [pow_add, div_mul_div_comm]
  simp_rw [he]
  simpa only [mul_zero] using h.const_mul (a^q / (q.factorial : ℝ))

theorem limitingSieveRemainder_tendsto_zero {L : ℕ} (q : Fin L → ℕ)
    (rates : Fin L → ℝ) :
    Tendsto (fun K => limitingSieveRemainder q K rates) atTop (𝓝 0) := by
  have h := tendsto_finset_prod (Finset.univ : Finset (Fin L)) (fun ell _ =>
    (tendsto_const_nhds (x := (1 : ℝ))).add (factorial_remainder_tendsto_zero (rates ell) (q ell)))
  simpa only [limitingSieveRemainder, add_zero, Finset.prod_const_one, sub_self] using h.sub_const 1

theorem count_sieve_series_limit (a : ℝ) (q : ℕ) :
    Tendsto (fun K : ℕ => ∑ j : Fin (K+1),
      (-1 : ℝ)^j.val * a^(q+j.val) / ((q.factorial : ℝ) * (j.val.factorial : ℝ))) atTop
      (𝓝 (Real.exp (-a) * a^q / (q.factorial : ℝ))) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp (-a)).mul_left (a^q / (q.factorial : ℝ))
  rw [← Real.exp_eq_exp_ℝ] at hs
  have h := (tendsto_add_atTop_iff_nat 1).mpr hs.tendsto_sum_nat
  have he (K : ℕ) : (∑ j : Fin (K+1),
      (-1 : ℝ)^j.val * a^(q+j.val) / ((q.factorial : ℝ) * (j.val.factorial : ℝ))) =
      ∑ j ∈ Finset.range (K+1), (a^q / (q.factorial : ℝ)) * ((-a)^j / (j.factorial : ℝ)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      (-1 : ℝ)^j * a^(q+j) / ((q.factorial : ℝ) * (j.factorial : ℝ))) (K+1)]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add, neg_pow]
    ring
  simp_rw [he]
  convert h using 1 <;> congr 1 <;> ring

theorem count_vector_sieve_series_limit {L : ℕ} (q : Fin L → ℕ)
    (rates : Fin L → ℝ) :
    Tendsto (fun K : ℕ => ∏ ell, ∑ j : Fin (K+1),
      (-1 : ℝ)^j.val * rates ell ^ (q ell+j.val) /
        (((q ell).factorial : ℝ) * (j.val.factorial : ℝ))) atTop
      (𝓝 (∏ ell, Real.exp (-rates ell) * rates ell ^ q ell / ((q ell).factorial : ℝ))) :=
  tendsto_finset_prod _ (fun ell _ => count_sieve_series_limit (rates ell) (q ell))

end Luce
