import Luce.Section6CriticalPopulationEstimates

noncomputable section
open Set
namespace Luce.Section6

def criticalProbeTime (n m : ℕ) (k : ℝ) : ℝ := k*((m : ℝ)/n)/Real.log ((n : ℝ)/m)

theorem critical_probe_log {k x z : ℝ} (hk : 0 < k) (hx : 0 < x) (hz : 0 < z) :
    Real.log (1/(k*x/z)) = Real.log (1/x)+Real.log z-Real.log k := by
  rw [one_div,Real.log_inv,Real.log_div (mul_pos hk hx).ne' hz.ne',Real.log_mul hk.ne' hx.ne',
    one_div,Real.log_inv]
  ring

/-- Exact algebraic form of the population estimates at coarse critical
probe times. These times need not be finite-population quantiles. -/
theorem CriticalProfile.probe_estimates {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (grid : SamplingGrid) (w : WeightArray),
      SampledRates grid w f → ∀ (n m : ℕ), 1 ≤ m → m ≤ n →
      ∀ k : ℝ, 0 < k → k ≤ Real.log ((n : ℝ)/m) →
      |(n : ℝ)*populationG (w n) (criticalProbeTime n m k) -
        (c*k*m/Real.log ((n : ℝ)/m)) *
          (Real.log ((n : ℝ)/m)+Real.log (Real.log ((n : ℝ)/m))-Real.log k)| ≤
        C*k*m/Real.log ((n : ℝ)/m)+1 ∧
      (n : ℝ)*populationD (w n) 1 (criticalProbeTime n m k) ≤
        c*n*(Real.log ((n : ℝ)/m)+Real.log (Real.log ((n : ℝ)/m))-Real.log k)+C*n+
          2*Real.exp (-1)*n*Real.log ((n : ℝ)/m)/(k*m) := by
  obtain ⟨C,hC,hbound⟩ := hp.population_estimates
  refine ⟨C,hC,?_⟩
  intro grid w hw n m hm hmn k hk hkz
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < m) hmn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hz : 0 < Real.log ((n : ℝ)/m) := hk.trans_le hkz
  have hx : 0 < (m : ℝ)/n := div_pos hm0 hn0
  have ht : 0 < criticalProbeTime n m k := div_pos (mul_pos hk hx) hz
  have ht1 : criticalProbeTime n m k ≤ 1 := by
    apply (div_le_one hz).mpr
    exact (mul_le_of_le_one_right hk.le ((div_le_one hn0).mpr (by exact_mod_cast hmn))).trans hkz
  have hlog : Real.log (1/criticalProbeTime n m k) =
      Real.log ((n : ℝ)/m)+Real.log (Real.log ((n : ℝ)/m))-Real.log k := by
    rw [criticalProbeTime,critical_probe_log hk hx hz,one_div_div]
  obtain ⟨hG,hD⟩ := hbound grid w hw n hn _ ht ht1
  rw [hlog] at hG hD
  constructor
  · have h := mul_le_mul_of_nonneg_left hG hn0.le
    rw [show (n : ℝ)*|populationG (w n) (criticalProbeTime n m k) -
      c*criticalProbeTime n m k*(Real.log ((n : ℝ)/m)+Real.log (Real.log ((n : ℝ)/m))-Real.log k)| =
      |(n : ℝ)*(populationG (w n) (criticalProbeTime n m k) -
      c*criticalProbeTime n m k*(Real.log ((n : ℝ)/m)+Real.log (Real.log ((n : ℝ)/m))-Real.log k))|
        by rw [abs_mul,abs_of_pos hn0]] at h
    convert h using 1 <;> first | rfl | (dsimp [criticalProbeTime]; field_simp <;> ring)
  · have h := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hD) hn0.le
    have heq : (n : ℝ)*(C+2*Real.exp (-1)/(n*criticalProbeTime n m k)) =
        C*n+2*Real.exp (-1)*n*Real.log ((n : ℝ)/m)/(k*m) := by
      dsimp [criticalProbeTime]
      field_simp
    rw [heq] at h
    nlinarith only [h]

end Luce.Section6
