import Luce.Section6EndpointBounds
import Luce.Section6MonotoneQuadrature

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Luce.Section6

theorem samplePoint_le_label (grid : SamplingGrid) {n : ℕ} (i : Fin n) :
    samplePoint grid n i ≤ ((i.val : ℝ)+1)/(n : ℝ) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  apply (le_div_iff₀ hn).mpr
  simpa only [mul_comm] using (samplePoint_scaled_cell grid i).2

/-- Every label in a sufficiently short initial block has the same
derived power lower bound. No monotonicity of the profile is required. -/
theorem PowerProfile.left_initial_block_rate_floor {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ eps : ℝ, 0 < eps ∧ eps < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n k : ℕ), 0 < n → (k : ℝ)/(n : ℝ) < eps →
    ∀ i : Fin n, i.val+1 ≤ k →
      (c/2)*((k : ℝ)/(n : ℝ))^(-alpha) ≤ (w n).rate i := by
  have hc := hp.2.2.1.1
  have ha := hp.2.2.1.2.1
  obtain ⟨delta, hd, hdelta⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hp.left_eventually_comparable
  change 0 < delta at hd
  refine ⟨min (delta/2) (1/2), lt_min (half_pos hd) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro grid w hw n k hn hk i hi
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs := samplePoint_mem grid i
  have hle : samplePoint grid n i ≤ (k : ℝ)/(n : ℝ) := by
    refine (samplePoint_le_label grid i).trans (div_le_div_of_nonneg_right ?_ hnR.le)
    exact_mod_cast hi
  have hsd : samplePoint grid n i < delta :=
    hle.trans_lt (hk.trans ((min_le_left _ _).trans_lt (by linarith)))
  have hpow := Real.rpow_le_rpow_of_nonpos hs.1 hle (by linarith : -alpha ≤ 0)
  exact (mul_le_mul_of_nonneg_left hpow (half_pos hc).le).trans
    (by simpa only [← hw n i] using (hdelta ⟨hs.1, hsd⟩).1)

end Luce.Section6
