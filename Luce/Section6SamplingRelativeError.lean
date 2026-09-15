import Luce.Section6RightRateFloor
import Luce.Section6LeftRateFloor
import Luce.Section6PowerInverseBounds

noncomputable section
open Set
namespace Luce.Section6

theorem samplePoint_ratio_interval (grid : SamplingGrid) {n : ℕ} (i : Fin n) :
    samplePoint grid n i / (((i.val : ℝ)+1)/(n : ℝ)) ∈ Icc (1/2 : ℝ) 1 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hx : 0 < ((i.val : ℝ)+1)/(n : ℝ) := by positivity
  exact ⟨(le_div_iff₀ hx).mpr (samplePoint_ge_half_label grid i),
    (div_le_one hx).mpr (samplePoint_le_label grid i)⟩

/-- The midpoint shift and the interior denominator shift both cost
at most the reciprocal of the one-based label. -/
theorem samplePoint_relative_error (grid : SamplingGrid) {n : ℕ} (i : Fin n) :
    |samplePoint grid n i / (((i.val : ℝ)+1)/(n : ℝ))-1| ≤ 1/((i.val : ℝ)+1) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hm : (0 : ℝ) < (i.val : ℝ)+1 := by positivity
  have hi : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
  have hr := samplePoint_ratio_interval grid i
  rw [abs_of_nonpos (sub_nonpos.mpr hr.2)]
  cases grid
  · have heq : samplePoint .midpoint n i / (((i.val : ℝ)+1)/(n : ℝ)) =
        1-1/(2*((i.val : ℝ)+1)) := by
      dsimp [samplePoint]
      field_simp
      ring
    rw [heq]
    have hh : 0 ≤ 1/((i.val : ℝ)+1) := by positivity
    have hid : 1/(2*((i.val : ℝ)+1)) = (1/((i.val : ℝ)+1))/2 := by field_simp
    rw [hid]
    linarith
  · have heq : samplePoint .interior n i / (((i.val : ℝ)+1)/(n : ℝ)) =
        (n : ℝ)/((n : ℝ)+1) := by
      dsimp [samplePoint]
      field_simp
    rw [heq]
    have hid : -((n : ℝ)/((n : ℝ)+1)-1) = 1/((n : ℝ)+1) := by
      field_simp
      ring
    rw [hid]
    exact one_div_le_one_div_of_le hm (by linarith)

theorem samplePoint_power_relative_error (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (grid : SamplingGrid) (n : ℕ) (i : Fin n),
      |(samplePoint grid n i)^r / ((((i.val : ℝ)+1)/(n : ℝ))^r)-1| ≤
        C/((i.val : ℝ)+1) := by
  obtain ⟨C, hC, hbound⟩ := rpow_relative_lipschitz r
  refine ⟨C, hC, ?_⟩
  intro grid n i
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hx : 0 < ((i.val : ℝ)+1)/(n : ℝ) := by positivity
  have hr := samplePoint_ratio_interval grid i
  have hh := hbound _ ⟨hr.1, hr.2.trans (by norm_num)⟩
  rw [Real.div_rpow (samplePoint_mem grid i).1.le hx.le] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (samplePoint_relative_error grid i) hC.le).trans_eq (by ring))

end Luce.Section6
