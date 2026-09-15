import Luce.Section6PopulationPowerBounds
import Luce.Section6WeightedIntegrals

noncomputable section
namespace Luce.Section6

/-- An outside-source positive rate floor absorbs the inverse target-depth
factor into inverse row size. This is a numerical helper, not a model assumption. -/
theorem outside_right_kernel_inverse_row {beta b d : ℝ}
    (hbeta : 0 < beta) (hb : 0 < b) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n h theta : ℝ, 0 < n → 0 < h → b ≤ theta →
      (theta*(n/h)^beta/h)*Real.exp (-d*(theta*(n/h)^beta)) ≤ C/n := by
  obtain ⟨D, hD, hdecay⟩ := exponential_le_power
    (a := 1/beta) (by positivity) (d := (d/2)*b) (by positivity)
  let A : ℝ := Real.exp (-1)/(d/2)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A*D, mul_pos hA hD, ?_⟩
  intro n h theta hn hh htheta
  have hy : 0 < n/h := div_pos hn hh
  have hyp : 0 < (n/h)^beta := Real.rpow_pos_of_pos hy _
  have hk := rateKernel_bound_above_lower hd
    (mul_le_mul_of_nonneg_right htheta hyp.le)
  have hk' : (theta*(n/h)^beta)*Real.exp (-d*(theta*(n/h)^beta)) ≤
      A*Real.exp (-((d/2)*b)*((n/h)^beta)) := by
    simpa only [rateKernel, survivalKernel, A, mul_assoc, neg_mul] using hk
  have hp : ((n/h)^beta)^(-(1/beta)) = h/n := by
    rw [← Real.rpow_mul hy.le]
    have he : beta * (-(1/beta)) = -1 := by field_simp
    rw [he, Real.rpow_neg_one]
    simp
  have he := hdecay ((n/h)^beta) hyp
  rw [hp] at he
  have he' : Real.exp (-((d/2)*b)*((n/h)^beta)) ≤ D*(h/n) := by
    simpa only [neg_mul] using he
  have hbound := hk'.trans (mul_le_mul_of_nonneg_left he' hA.le)
  have ht := div_le_div_of_nonneg_right hbound hh.le
  have hid : (A*(D*(h/n)))/h = (A*D)/n := by field_simp
  simpa only [div_mul_eq_mul_div, hid] using ht

end Luce.Section6
