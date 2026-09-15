import Luce.Section1Sukhatme

/-! The target imports definitions only; the proof must inhabit it without
any further profile, sampling, moment, or convergence hypotheses. -/
example : Luce.Sukhatme.Corollary19 := Luce.Sukhatme.corollary19

/-- The real-valued rate is literally the natural-valued standard rate. -/
example (n : ℕ) (i : Fin n) :
    (Luce.Sukhatme.weights n).rate i = ((n - i.val : ℕ) : ℝ) := by
  simp only [Luce.Sukhatme.weights, Nat.cast_sub i.isLt.le]

#print Luce.Sukhatme.Corollary19
#print axioms Luce.Sukhatme.corollary19
#print axioms Luce.Sukhatme.profile
#print axioms Luce.Sukhatme.sampled_rates
#print axioms Luce.Sukhatme.sampled_mass
#print axioms Luce.Sukhatme.density_eq_incrementDensity
#print axioms Luce.Sukhatme.convolution_eq
#print axioms Luce.Sukhatme.coefficient_zero
#print axioms Luce.Sukhatme.coefficient_one_integral
#print axioms Luce.Sukhatme.bessel_integrand_integrable
#print axioms Luce.Sukhatme.coefficient_one
#print axioms Luce.Sukhatme.gaussian_spatial_reindex
