import Luce.Section6CriticalInsertionLp
import Luce.Section6DominationMatrix
import Luce.Section6GapOffsets

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Luce.Section6

theorem critical_shift_log_bounds {n m q : ℝ} (hn : 0 < n) (hm : 0 < m) (hq : 0 < q)
    (hmq : m ≤ 2*q) (hqm : q ≤ 2*m)
    (hz : 2*Real.log 2 ≤ Real.log (n/m)) :
    Real.log (n/m)/2 ≤ Real.log (n/q) ∧ Real.log (n/q) ≤ 2*Real.log (n/m) := by
  have h1 := Real.log_le_log hm hmq
  have h2 := Real.log_le_log hq hqm
  rw [Real.log_mul (by norm_num) hq.ne'] at h1
  rw [Real.log_mul (by norm_num) hm.ne'] at h2
  rw [Real.log_div hn.ne' hm.ne'] at hz
  rw [Real.log_div hn.ne' hm.ne',Real.log_div hn.ne' hq.ne']
  constructor <;> linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]

/-- The actual insertion domination matrix has a critical exponential
kernel bound above a fixed rank cutoff. -/
theorem CriticalProfile.critical_domination_matrix {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) (r : ℕ) (hr : 1 ≤ r) :
    ∃ K gamma Z : ℝ, 0 < K ∧ 0 < gamma ∧ 2 ≤ Z ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (i j : Fin n), 8*r+8 ≤ j.val+1 → 8*(j.val+1) ≤ n →
      Z ≤ Real.log ((n : ℝ)/((j.val : ℝ)+1)) →
      insertionDominationMatrix (w n) r r i j ≤
        K/(((i.val : ℝ)+1)*Real.log ((n : ℝ)/((j.val : ℝ)+1)))*
          Real.exp (-gamma*(((j.val : ℝ)+1)/
            (((i.val : ℝ)+1)*Real.log ((n : ℝ)/((j.val : ℝ)+1))))) := by
  obtain ⟨K,gamma,Z,hK,hgamma,hZ,hbound⟩ := hp.critical_insertion_Lp r hr
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨2*K,gamma/4,2*Z+2*Real.log 2,by positivity,by positivity,by linarith,?_⟩
  intro grid w hw n i j hj hjn hz
  obtain ⟨removed,q,hremoved,hshift,heq⟩ := insertionDominationMatrix_attained (w n) r r i j
  have hshift' : Nat.dist q ((j.val+1)-1) ≤ r+1 := by simpa using hshift
  obtain ⟨hq,hqm,hmq⟩ := shifted_left_gap_bounds hj hshift'
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
  have hqcard : q < (Finset.univ \ removed).card := by
    rw [hcard]
    exact shifted_left_nonterminal hremoved hj (by omega) hshift'
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmp : (0 : ℝ) < (j.val : ℝ)+1 := by positivity
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hip : (0 : ℝ) < (i.val : ℝ)+1 := by positivity
  let z := Real.log ((n : ℝ)/((j.val : ℝ)+1))
  let zq := Real.log ((n : ℝ)/q)
  have hz2 : 2 ≤ z := by dsimp [z]; linarith
  have hzp : 0 < z := by linarith
  have hlogs := critical_shift_log_bounds hnp hmp hqp (by exact_mod_cast hmq)
    (by exact_mod_cast hqm) (by dsimp [z] at hz2; linarith)
  have hzq : Z ≤ zq := by dsimp [zq]; linarith [hlogs.1]
  have hzqp : 0 < zq := by linarith
  have hb := hbound grid w hw n removed ⟨q,hqcard⟩ i (by dsimp; omega)
    (by dsimp; omega) (by dsimp; omega) hzq
  rw [← heq] at hb
  have hb' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (insertionDominationMatrix_nonneg _ _ _ _ _),
    ENNReal.toReal_ofReal (by positivity)] at hb'
  apply hb'.trans
  have hpre : K/(((i.val : ℝ)+1)*zq) ≤ (2*K)/(((i.val : ℝ)+1)*z) := by
    apply (div_le_div_iff₀ (mul_pos hip hzqp) (mul_pos hip hzp)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogs.1 (mul_pos hK hip).le]
  have hex : Real.exp (-gamma*((q : ℝ)/(((i.val : ℝ)+1)*zq))) ≤
      Real.exp (-(gamma/4)*(((j.val : ℝ)+1)/(((i.val : ℝ)+1)*z))) := by
    apply Real.exp_le_exp.mpr
    have hmqR : (j.val : ℝ)+1 ≤ 2*q := by exact_mod_cast hmq
    have hratio : ((j.val : ℝ)+1)/(4*(((i.val : ℝ)+1)*z)) ≤
        (q : ℝ)/(((i.val : ℝ)+1)*zq) := by
      apply (div_le_div_iff₀ (by positivity) (mul_pos hip hzqp)).mpr
      have h1 := mul_le_mul_of_nonneg_left hlogs.2 (mul_pos hmp hip).le
      have h2 := mul_le_mul_of_nonneg_right hmqR (mul_pos hip hzp).le
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hratio hgamma.le
    have hid : -(gamma/4)*(((j.val : ℝ)+1)/(((i.val : ℝ)+1)*z)) =
        -(gamma*(((j.val : ℝ)+1)/(4*(((i.val : ℝ)+1)*z)))) := by field_simp
    rw [hid]
    simpa only [neg_mul] using neg_le_neg hh
  exact mul_le_mul hpre hex (Real.exp_pos _).le (by positivity)

end Luce.Section6
