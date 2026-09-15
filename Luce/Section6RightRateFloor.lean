import Luce.Section6InactiveBounds
import Luce.Section4EndpointShells

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

theorem samplePoint_ge_half_label (grid : SamplingGrid) {n : ℕ} (i : Fin n) :
    (1/2 : ℝ)*(((i.val : ℝ)+1)/(n : ℝ)) ≤ samplePoint grid n i := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  rw [show (1/2 : ℝ)*(((i.val : ℝ)+1)/(n : ℝ)) = ((i.val : ℝ)+1)/(2*(n : ℝ)) by ring]
  cases grid <;> simp only [samplePoint]
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2*(n : ℝ)) hnR).mpr
    nlinarith [mul_nonneg hi0 hnR.le]
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2*(n : ℝ)) (by positivity)).mpr
    have hh := mul_nonneg (by linarith : (0 : ℝ) ≤ (i.val : ℝ)+1) (sub_nonneg.mpr hn1)
    nlinarith

/-- Global lower power bound obtained from endpoint comparability and
positivity away from the active right endpoint. -/
theorem PowerProfile.right_global_lower_power {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Ioo (0 : ℝ) 1, C*s^beta ≤ f (1-s) := by
  have hc := h.2.2.2.1.1
  have hb := h.2.2.2.1.2.1
  obtain ⟨delta, hd, hdelta⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h.right_eventually_comparable
  change 0 < delta at hd
  let eps := min (delta/2) (1/4)
  have heps : 0 < eps := lt_min (half_pos hd) (by norm_num)
  have heps1 : eps < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hepsd : eps < delta := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨d, hd0, hoff⟩ := h.lower_away_right heps heps1
  refine ⟨min (c/2) d, lt_min (half_pos hc) hd0, ?_⟩
  intro s hs
  by_cases hnear : s < eps
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_pos_of_pos hs.1 beta).le).trans
      (hdelta ⟨hs.1, hnear.trans hepsd⟩).1
  · have hfar := hoff (1-s) ⟨by linarith [hs.2], by linarith [le_of_not_gt hnear]⟩
    have hpow : s^beta ≤ 1 := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow hs.1.le hs.2.le hb.le
    calc
      _ ≤ d*s^beta := mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_pos_of_pos hs.1 _).le
      _ ≤ d := by simpa using mul_le_mul_of_nonneg_left hpow hd0.le
      _ ≤ _ := hfar

/-- The manuscript's terminal-depth rate floor for both sampling grids.
terminalDepth i is the existing one-based depth n-i.val. -/
theorem PowerProfile.right_sampled_rate_floor {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ i : Fin n,
      C*((terminalDepth i : ℝ)/(n : ℝ))^beta ≤ (w n).rate i := by
  have hb := h.2.2.2.1.2.1
  obtain ⟨C, hC, hbound⟩ := h.right_global_lower_power
  refine ⟨C*(1/2 : ℝ)^beta, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro grid w hw n i
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd : (0 : ℝ) < terminalDepth i := Nat.cast_pos.mpr (terminalDepth_pos i)
  have hdepth : (i.rev.val : ℝ)+1 = (terminalDepth i : ℝ) := by
    exact_mod_cast (show i.rev.val+1 = terminalDepth i by rw [Fin.val_rev]; unfold terminalDepth; omega)
  have hs := samplePoint_ge_half_label grid i.rev
  rw [hdepth] at hs
  have hp := Real.rpow_le_rpow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (div_pos hd hnR).le) hs hb.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/2) (div_pos hd hnR).le] at hp
  have hh := hbound (samplePoint grid n i.rev) (samplePoint_mem grid i.rev)
  have heq : 1-samplePoint grid n i.rev = samplePoint grid n i := by rw [samplePoint_rev]; ring
  rw [heq, ← hw n i] at hh
  have hp' : C*(1/2 : ℝ)^beta*((terminalDepth i : ℝ)/(n : ℝ))^beta ≤
      C*(samplePoint grid n i.rev)^beta := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le
  exact hp'.trans hh

end Luce.Section6
