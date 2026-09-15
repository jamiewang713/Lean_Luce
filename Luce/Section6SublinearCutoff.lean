import Luce.Section6EnvelopeAbsorption

noncomputable section
open Filter Set
open scoped Topology
namespace Luce.Section6

/-- Both range requirements at a sublinear comparison depth are derived
as eventual properties, with no prescribed or uniform convergence rate. -/
theorem sublinear_power_cutoff {z H delta : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (hdelta : 0 < delta) :
    ∃ N : ℝ, 0 < N ∧ ∀ n : ℝ, N ≤ n →
      1 ≤ n ∧ H ≤ n^z ∧ n^z/n < delta := by
  have hlarge : ∀ᶠ n : ℝ in atTop, H ≤ n^z :=
    (tendsto_rpow_atTop hz).eventually (eventually_ge_atTop H)
  have hsmall : ∀ᶠ n : ℝ in atTop, n^(-(1-z)) < delta :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 1-z)).eventually (Iio_mem_nhds hdelta)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlarge.and hsmall)
  refine ⟨max 1 N, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  obtain ⟨hh, hs⟩ := hN n ((le_max_right _ _).trans hn)
  refine ⟨hn1, hh, ?_⟩
  have he : n^z/n = n^(-(1-z)) := by
    rw [show -(1-z) = z-1 by ring, Real.rpow_sub hn0, Real.rpow_one]
  rwa [he]

end Luce.Section6
