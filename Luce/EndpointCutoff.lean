import Luce.Endpoint
import Mathlib.Topology.Order.IntermediateValue

/-! # Existence and size of the mean-survivor cutoff -/

open scoped BigOperators Topology
open Real Set Filter

namespace Luce

theorem continuous_meanSurvivors {n : ℕ} (θ : Fin n → ℝ) :
    Continuous (meanSurvivors θ) := by
  apply continuous_finsetSum
  intro i hi
  exact Real.continuous_exp.comp (continuous_const.mul continuous_id)

theorem meanSurvivors_zero {n : ℕ} (θ : Fin n → ℝ) : meanSurvivors θ 0 = n := by
  simp [meanSurvivors]

theorem meanSurvivors_strictAnti {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) : StrictAnti (meanSurvivors θ) := by
  intro s t hst
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  · intro i hi
    apply Real.exp_lt_exp.mpr
    exact mul_lt_mul_of_neg_left hst (neg_neg_of_pos (hθ i))

theorem tendsto_meanSurvivors_atTop {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) : Tendsto (meanSurvivors θ) atTop (𝓝 0) := by
  have hlim : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Tendsto (fun t : ℝ => Real.exp (-θ i * t)) atTop (𝓝 0) := by
    intro i hi
    exact Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_neg_of_pos (hθ i)) tendsto_id)
  change Tendsto (fun t => ∑ i, Real.exp (-θ i * t)) atTop (𝓝 0)
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ hlim

/-- The cutoff used by the paper exists and is unique whenever `0 < B ≤ n`. -/
theorem exists_unique_meanSurvivors_cutoff {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) {B : ℝ} (hB : 0 < B) (hBn : B ≤ n) :
    ∃! s : ℝ, 0 ≤ s ∧ meanSurvivors θ s = B := by
  have hevent : ∀ᶠ t : ℝ in atTop, meanSurvivors θ t < B :=
    (tendsto_meanSurvivors_atTop θ hθ).eventually (Iio_mem_nhds hB)
  obtain ⟨T, hT, hsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and hevent).exists
  have hBmem : B ∈ Icc (meanSurvivors θ T) (meanSurvivors θ 0) := by
    rw [meanSurvivors_zero]
    exact ⟨hsmall.le, hBn⟩
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc' hT
    (continuous_meanSurvivors θ).continuousOn hBmem
  refine ⟨s, ⟨hs.1, heq⟩, ?_⟩
  intro t ht
  exact (meanSurvivors_strictAnti hn θ hθ).injective (ht.2.trans heq.symm)

/-- The lower bound on the cutoff stated in the proof of the endpoint bound. -/
theorem meanSurvivors_cutoff_log_lower {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = (n : ℝ))
    {s B : ℝ} (hs : 0 ≤ s) (hcut : meanSurvivors θ s = B) :
    (1 / 2 : ℝ) * Real.log ((n : ℝ) / (2 * B)) ≤ s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : 0 < B := hcut ▸ meanSurvivors_pos hn θ s
  have hb := meanSurvivors_lower_bound θ hθ hsum hs
  rw [hcut] at hb
  have hbase : Real.exp (-2 * s) ≤ 2 * B / n := by
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  have hlog := Real.log_le_log (Real.exp_pos _) hbase
  rw [Real.log_exp, Real.log_div (by positivity) (ne_of_gt hnR),
    Real.log_mul (by norm_num) (ne_of_gt hB)] at hlog
  rw [Real.log_div (ne_of_gt hnR) (by positivity),
    Real.log_mul (by norm_num) (ne_of_gt hB)]
  linarith

end Luce
