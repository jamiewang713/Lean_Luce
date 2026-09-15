import Luce.Section6CriticalProfilePerturbation

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Uniform comparison with the pole costs O(t) for arrivals and O(1)
for remaining weight. No smoothness of the profile is used. -/
theorem CriticalProfile.population_pole_comparison {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (grid : SamplingGrid) (w : WeightArray),
      SampledRates grid w f → ∀ (n : ℕ), 0 < n → ∀ t : ℝ, 0 ≤ t →
      |populationG (w n) t -
        (∑ i : Fin n, (1-survivalKernel t (c/samplePoint grid n i)))/n| ≤ C*t ∧
      |populationD (w n) 1 t -
        (∑ i : Fin n, rateKernel t (c/samplePoint grid n i))/n| ≤ C := by
  obtain ⟨C,hC,hbound⟩ := hp.sampled_error_average
  refine ⟨C,hC,?_⟩
  intro grid w hw n hn t ht
  have hc : 0 < c := hp.2.2.1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcs (i : Fin n) : 0 ≤ c/samplePoint grid n i :=
    div_nonneg hc.le (samplePoint_mem grid i).1.le
  constructor
  · unfold populationG
    rw [← sub_div,abs_div,abs_of_pos hn0,← Finset.sum_sub_distrib]
    calc
      _ ≤ (∑ i : Fin n, |(1-survivalKernel t ((w n).rate i))-
            (1-survivalKernel t (c/samplePoint grid n i))|)/n :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn0.le
      _ ≤ (∑ i : Fin n, t*|((w n).rate i)-c/samplePoint grid n i|)/n := by
        apply div_le_div_of_nonneg_right _ hn0.le
        apply Finset.sum_le_sum
        intro i _
        rw [show (1-survivalKernel t ((w n).rate i))-
          (1-survivalKernel t (c/samplePoint grid n i)) =
          -(survivalKernel t ((w n).rate i)-survivalKernel t (c/samplePoint grid n i)) by ring,
          abs_neg]
        exact abs_survivalKernel_sub_le ht ((w n).positive i).le (hcs i)
      _ = t*((∑ i : Fin n, |((w n).rate i)-c/samplePoint grid n i|)/n) := by
        rw [← Finset.mul_sum]; ring
      _ ≤ t*C := mul_le_mul_of_nonneg_left (hbound grid w hw n hn) ht
      _ = _ := mul_comm _ _
  · simp only [populationD,pow_one]
    change |(∑ i : Fin n, rateKernel t ((w n).rate i))/n -
      (∑ i : Fin n, rateKernel t (c/samplePoint grid n i))/n| ≤ C
    rw [← sub_div,abs_div,abs_of_pos hn0,← Finset.sum_sub_distrib]
    calc
      _ ≤ (∑ i : Fin n, |rateKernel t ((w n).rate i)-
          rateKernel t (c/samplePoint grid n i)|)/n :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn0.le
      _ ≤ (∑ i : Fin n, |((w n).rate i)-c/samplePoint grid n i|)/n := by
        apply div_le_div_of_nonneg_right _ hn0.le
        exact Finset.sum_le_sum fun i _ => abs_rateKernel_sub_le ht ((w n).positive i).le (hcs i)
      _ ≤ _ := hbound grid w hw n hn

end Luce.Section6
