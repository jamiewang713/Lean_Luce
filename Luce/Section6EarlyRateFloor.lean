import Luce.Section6LeftRemainingRate

noncomputable section
namespace Luce.Section6

/-- Removing a fixed number of labels leaves rate of order n^alpha at
an active left endpoint, including before any background arrival. -/
theorem PowerProfile.left_fixed_removal_rate_floor {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (s : ℕ) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ removed : Finset (Fin n), removed.card ≤ s →
      C*(n : ℝ)^alpha ≤ ∑ i ∈ Finset.univ \ removed, (w n).rate i := by
  obtain ⟨B, eps, hB, heps, heps1, hb⟩ := hp.left_remaining_rate_floor
  have hs : (0 : ℝ) < (s : ℝ)+1 := by positivity
  refine ⟨B*((s : ℝ)+1)^(1-alpha), 6*((s : ℝ)+1)/eps, by positivity, by positivity, ?_⟩
  intro grid w hw n hn hlarge removed hremoved
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn0 := (div_le_iff₀ heps).mp hlarge
  have hsmall : (3*((s+1 : ℕ) : ℝ))/(n : ℝ) < eps := by
    apply (div_lt_iff₀ hnR).mpr
    push_cast
    nlinarith
  have he := hb grid w hw n (s+1) hn (by omega) hsmall removed (by omega)
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm, mul_left_comm] using he

end Luce.Section6
