import Luce.Section6ProfileDefinitions
import Mathlib.Tactic

noncomputable section
open Set
namespace Luce.Section6

theorem samplePoint_mem (grid : SamplingGrid) {n : ℕ} (i : Fin n) :
    samplePoint grid n i ∈ Ioo (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  cases grid <;> simp only [samplePoint, mem_Ioo]
  · constructor
    · exact div_pos (by linarith) hn
    · exact (div_lt_one hn).mpr (by linarith)
  · constructor
    · exact div_pos (by linarith) (by linarith)
    · exact (div_lt_one (by linarith : (0 : ℝ) < n + 1)).mpr (by linarith)

/-- Both sampling grids give actual positive finite-model rates. -/
def sampledWeights (grid : SamplingGrid) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x) : WeightArray :=
  fun n => ⟨fun i => f (samplePoint grid n i), fun i => hf _ (samplePoint_mem grid i)⟩

theorem sampledWeights_sampled (grid : SamplingGrid) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x) :
    SampledRates grid (sampledWeights grid f hf) f := by
  intro n i
  rfl

/-- Reflection of a label preserves the chosen sampling grid. -/
theorem samplePoint_rev (grid : SamplingGrid) {n : ℕ} (i : Fin n) :
    samplePoint grid n i.rev = 1 - samplePoint grid n i := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt i.isLt)
  have hv : (i.rev.val : ℝ) + (i.val : ℝ) + 1 = n := by
    exact_mod_cast (show i.rev.val + i.val + 1 = n by simp only [Fin.val_rev]; omega)
  cases grid <;> simp only [samplePoint]
  · field_simp
    linarith
  · have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    linarith

end Luce.Section6
