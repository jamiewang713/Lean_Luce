import Luce.Section6SamplingRelativeError
import Luce.Section6EndpointBounds

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

/-- The original relative expansion survives either sampling shift with
the sharp additional reciprocal-label error. -/
theorem PowerExpansion.sampled_relative_error {g : ℝ → ℝ} {c p eta : ℝ}
    (h : PowerExpansion g c p eta) (hc : 0 < c) (heta : 0 < eta) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (n : ℕ) (i : Fin n),
      ((i.val : ℝ)+1)/(n : ℝ) < delta →
      |g (samplePoint grid n i)/(c*((((i.val : ℝ)+1)/(n : ℝ))^p))-1| ≤
        C*((((i.val : ℝ)+1)/(n : ℝ))^eta+1/((i.val : ℝ)+1)) := by
  obtain ⟨B, hB, hb⟩ := h.exists_pos
  have hevent : ∀ᶠ s in 𝓝[>] (0 : ℝ), |g s/(c*s^p)-1| ≤ B*s^eta := by
    filter_upwards [hb.bound, self_mem_nhdsWithin] with s hs hs0
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hs0 eta)] using hs
  obtain ⟨d, hd, hnear⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  change 0 < d at hd
  obtain ⟨P, hP, hshift⟩ := samplePoint_power_relative_error p
  let E := B*(P+1)
  have hE : 0 < E := mul_pos hB (by linarith)
  refine ⟨E+P, min (d/2) (1/2), add_pos hE hP, lt_min (half_pos hd) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro grid n i hi
  let s := samplePoint grid n i
  let x := ((i.val : ℝ)+1)/(n : ℝ)
  let m := (i.val : ℝ)+1
  have hs : 0 < s := (samplePoint_mem grid i).1
  have hm : 0 < m := by dsimp [m]; positivity
  have hm1 : 1 ≤ m := by dsimp [m]; have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hx : 0 < x := div_pos hm hn
  have hsx : s ≤ x := samplePoint_le_label grid i
  have hsd : s < d := hsx.trans_lt (hi.trans ((min_le_left _ _).trans_lt (by linarith)))
  let u := g s/(c*s^p)
  let v := s^p/x^p
  have hv : 0 < v := div_pos (Real.rpow_pos_of_pos hs _) (Real.rpow_pos_of_pos hx _)
  have hu : |u-1| ≤ B*x^eta :=
    (hnear ⟨hs, hsd⟩).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le hsx heta.le) hB.le)
  have hvErr : |v-1| ≤ P/m := hshift grid n i
  have hvUpper : v ≤ P+1 := by
    have hh := (abs_le.mp hvErr).2
    have hdiv : P/m ≤ P := (div_le_iff₀ hm).mpr (by nlinarith)
    linarith
  have hid : u*v = g s/(c*x^p) := by
    dsimp [u, v]
    field_simp
  have herr : |g s/(c*x^p)-1| ≤ E*x^eta+P/m := by
    calc
      _ = |(u-1)*v+(v-1)| := by rw [show (u-1)*v+(v-1) = u*v-1 by ring, hid]
      _ ≤ |u-1| * v+|v-1| := by simpa only [abs_mul, abs_of_pos hv] using abs_add_le ((u-1)*v) (v-1)
      _ ≤ (B*x^eta)*(P+1)+P/m := add_le_add
        (mul_le_mul hu hvUpper hv.le (mul_nonneg hB.le (Real.rpow_pos_of_pos hx eta).le)) hvErr
      _ = _ := by dsimp [E]; ring
  change |g s/(c*x^p)-1| ≤ (E+P)*(x^eta+1/m)
  refine herr.trans ?_
  have h1 := mul_nonneg hE.le (one_div_nonneg.mpr hm.le)
  have h2 := mul_nonneg hP.le (Real.rpow_pos_of_pos hx eta).le
  rw [div_eq_mul_one_div P]
  nlinarith

end Luce.Section6
