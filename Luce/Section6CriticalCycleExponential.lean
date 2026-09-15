import Luce.Section6CriticalCycleDrop
import Luce.Section6CriticalRangeDecay

noncomputable section
open scoped BigOperators
namespace Luce.Section6

def criticalCycleDecay (k : ℕ) : ℝ := 1/(8*((k : ℝ)+1)^2)

theorem critical_cycle_decay_pos (k : ℕ) : 0 < criticalCycleDecay k := by
  unfold criticalCycleDecay
  positivity

theorem critical_log_cycle_exponential {gamma : ℝ} (hg : 0 < gamma) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z → ∀ y : Fin k → ℝ, (∀ i, 0 ≤ y i) →
      Real.exp (-gamma*(∑ a : Fin (k+1),
        Real.exp ((Fin.cons 0 y : Fin (k+1) → ℝ) a-(Fin.snoc y 0 : Fin (k+1) → ℝ) a)/
          (z+(Fin.snoc y 0 : Fin (k+1) → ℝ) a))) ≤
      C*z^(1/2 : ℝ)*(∏ i, Real.exp (-criticalCycleDecay k*y i)) := by
  let d : ℝ := 2*((k : ℝ)+1)^2
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨C,hC,hdecay⟩ := critical_range_decay hg hd
  refine ⟨C,hC,?_⟩
  intro z hz y hy
  let R := ∑ i, y i
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => hy i)
  have hzp : 0 < z := by linarith
  have hyt (a : Fin (k+1)) : 0 ≤ (Fin.snoc y 0 : Fin (k+1) → ℝ) a ∧
      (Fin.snoc y 0 : Fin (k+1) → ℝ) a ≤ R := by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simpa only [Fin.snoc_last] using And.intro (show (0 : ℝ) ≤ 0 from le_rfl) hR
    · simp only [Fin.snoc_castSucc]
      exact ⟨hy i,Finset.single_le_sum (fun i _ => hy i) (Finset.mem_univ i)⟩
  obtain ⟨a,ha⟩ := critical_cycle_one_drop k y hy
  have hsum : Real.exp (R/d)/(z+R) ≤ ∑ j : Fin (k+1),
      Real.exp ((Fin.cons 0 y : Fin (k+1) → ℝ) j-(Fin.snoc y 0 : Fin (k+1) → ℝ) j)/
        (z+(Fin.snoc y 0 : Fin (k+1) → ℝ) j) := by
    apply le_trans _ (Finset.single_le_sum (fun j _ =>
      div_nonneg (Real.exp_pos _).le (add_pos_of_pos_of_nonneg hzp (hyt j).1).le) (Finset.mem_univ a))
    exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ha) (by positivity)).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le
        (add_pos_of_pos_of_nonneg hzp (hyt a).1) (add_le_add le_rfl (hyt a).2))
  have hex := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hsum hg.le))
  have hh := hex.trans (by simpa only [neg_mul] using hdecay z R hz hR)
  have he : Real.exp (-R/(4*d)) = ∏ i, Real.exp (-criticalCycleDecay k*y i) := by
    rw [← Real.exp_sum]
    congr 1
    dsimp [R,d,criticalCycleDecay]
    rw [← Finset.mul_sum]
    ring
  rw [he] at hh
  simpa only [neg_mul] using hh

end Luce.Section6
