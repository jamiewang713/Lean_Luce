import Luce.Section6Sampling
import Mathlib.Analysis.SumIntegralComparisons

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem sum_endpoint_difference (g : ℝ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, g (i : ℝ)) -
      (∑ i ∈ Finset.range n, g ((i : ℝ)+1)) = g 0-g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    linarith

/-- Any selection within each unit cell has quadrature error bounded by
the total drop of an antitone function. No continuity is required. -/
theorem antitone_cell_sum_error {g : ℝ → ℝ} (n : ℕ)
    (hg : AntitoneOn g (Icc (0 : ℝ) n)) (s : Fin n → ℝ)
    (hs : ∀ i, (i.val : ℝ) ≤ s i ∧ s i ≤ (i.val : ℝ)+1) :
    |(∑ i, g (s i)) - ∫ x in (0 : ℝ)..n, g x| ≤ g 0-g n := by
  have hg' : AntitoneOn g (Icc (0 : ℝ) (0+n)) := by simpa using hg
  have hU := hg'.integral_le_sum (x₀ := 0) (a := n)
  have hL := hg'.sum_le_integral (x₀ := 0) (a := n)
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at hU hL
  have hU' : (∑ i, g (s i)) ≤ ∑ i : Fin n, g (i.val : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    have hi : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
    exact hg ⟨Nat.cast_nonneg _, by linarith⟩
      ⟨(Nat.cast_nonneg _).trans (hs i).1, (hs i).2.trans hi⟩ (hs i).1
  have hL' : (∑ i : Fin n, g ((i.val : ℝ)+1)) ≤ ∑ i, g (s i) := by
    apply Finset.sum_le_sum
    intro i _
    have hi : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
    exact hg ⟨(Nat.cast_nonneg _).trans (hs i).1, (hs i).2.trans hi⟩
      ⟨by positivity, hi⟩ (hs i).2
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => g (i : ℝ)) n] at hU'
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => g ((i : ℝ)+1)) n] at hL'
  have hd := sum_endpoint_difference g n
  rw [abs_le]
  constructor <;> linarith

/-- Both manuscript grids select one point in each of the original n cells.
This lets monotone-envelope quadrature use the same divisor n for either grid. -/
theorem samplePoint_scaled_cell (grid : SamplingGrid) {n : ℕ} (i : Fin n) :
    (i.val : ℝ) ≤ (n : ℝ)*samplePoint grid n i ∧
      (n : ℝ)*samplePoint grid n i ≤ (i.val : ℝ)+1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hi : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
  have hi0 := Nat.cast_nonneg (α := ℝ) i.val
  cases grid <;> simp only [samplePoint]
  · have heq : (n : ℝ)*(((i.val : ℝ)+1/2)/n) = (i.val : ℝ)+1/2 := by field_simp
    rw [heq]
    constructor <;> linarith
  · have hn1 : (0 : ℝ) < (n : ℝ)+1 := by linarith
    rw [← mul_div_assoc]
    constructor
    · apply (le_div_iff₀ hn1).mpr
      nlinarith
    · apply (div_le_iff₀ hn1).mpr
      nlinarith

theorem antitone_sample_average_error (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {g : ℝ → ℝ} (hg : AntitoneOn g (Icc (0 : ℝ) 1)) :
    |(∑ i : Fin n, g (samplePoint grid n i))/(n : ℝ) - ∫ x in (0 : ℝ)..1, g x| ≤
      (g 0-g 1)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscaled : AntitoneOn (fun x : ℝ => g (x/n)) (Icc (0 : ℝ) n) := by
    intro x hx y hy hxy
    exact hg ⟨div_nonneg hx.1 hnR.le, (div_le_one hnR).mpr hx.2⟩
      ⟨div_nonneg hy.1 hnR.le, (div_le_one hnR).mpr hy.2⟩
      (div_le_div_of_nonneg_right hxy hnR.le)
  have h := antitone_cell_sum_error n hscaled
    (fun i => (n : ℝ)*samplePoint grid n i) (samplePoint_scaled_cell grid)
  have hint : (∫ x in (0 : ℝ)..n, g (x/n)) = (n : ℝ)*(∫ x in (0 : ℝ)..1, g x) := by
    rw [intervalIntegral.integral_comp_div _ hnR.ne']
    simp [hnR.ne', smul_eq_mul]
  simp only [mul_div_cancel_left₀ _ hnR.ne', zero_div, div_self hnR.ne'] at h
  rw [hint] at h
  have hh := div_le_div_of_nonneg_right h hnR.le
  rw [← abs_of_pos hnR, ← abs_div] at hh
  have heq : ((∑ i : Fin n, g (samplePoint grid n i)) -
      (n : ℝ)*(∫ x in (0 : ℝ)..1, g x))/(n : ℝ) =
      (∑ i : Fin n, g (samplePoint grid n i))/(n : ℝ) - ∫ x in (0 : ℝ)..1, g x := by
    rw [sub_div, mul_div_cancel_left₀ _ hnR.ne']
  simpa only [heq, abs_of_pos hnR] using hh

end Luce.Section6
