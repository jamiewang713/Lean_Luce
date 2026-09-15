import Luce.Section6CriticalDeletedFloor
import Luce.Section6CriticalGapSurvival
import Luce.Section6RateFloorLp

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Luce.Section6

theorem CriticalProfile.critical_insertion_Lp {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) (p : ℕ) (hp1 : 1 ≤ p) :
    ∃ K gamma Z : ℝ, 0 < K ∧ 0 < gamma ∧ 2 ≤ Z ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card) (i : Fin n),
      4 ≤ q.val → removed.card ≤ q.val → 4*q.val ≤ n → Z ≤ Real.log ((n : ℝ)/q.val) →
      eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n)) ≤
        ENNReal.ofReal (K/(((i.val : ℝ)+1)*Real.log ((n : ℝ)/q.val))*
          Real.exp (-gamma*((q.val : ℝ)/(((i.val : ℝ)+1)*Real.log ((n : ℝ)/q.val))))) := by
  obtain ⟨Zf,hZf,hfloor⟩ := hp.deleted_remaining_floor
  obtain ⟨gamma,Zs,hgamma,hZs,hsurv⟩ := hp.deleted_gap_survival
  obtain ⟨a,b,ha,hb,hrates⟩ := hp.sampled_global_comparison
  have hc : 0 < c := hp.2.2.1
  have hpp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  let K := (2*(p.factorial : ℝ))*(2*b/c)
  refine ⟨K,gamma/p,max Zf Zs,by dsimp [K]; positivity,by positivity,
    hZf.trans (le_max_left _ _),?_⟩
  intro grid w hw n removed q i hq hr hqn hz
  let z := Real.log ((n : ℝ)/q.val)
  let x := (q.val : ℝ)/(((i.val : ℝ)+1)*z)
  let W := (c/2)*n*z
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hzp : 0 < z := by have := hZf.trans ((le_max_left _ _).trans hz); dsimp [z]; linarith
  have hi : (0 : ℝ) < (i.val : ℝ)+1 := by positivity
  have hwi := (w n).positive i
  have hW : 0 < W := by dsimp [W]; positivity
  have hf := hfloor grid w hw n removed q (by omega) hr hqn ((le_max_left _ _).trans hz)
  have hs := hsurv grid w hw n removed q i p hq (by omega) hp1 ((le_max_right _ _).trans hz)
  have hratio : (w n).rate i/W ≤ (2*b/c)*(1/(((i.val : ℝ)+1)*z)) := by
    calc
      _ ≤ (b*n/((i.val : ℝ)+1))/W := div_le_div_of_nonneg_right (hrates grid w hw n i).2 hW.le
      _ = _ := by dsimp [W]; field_simp
  have hm := deleted_kernel_moment_bound_of_rate_floor (w n) removed i q p hW hf
  have htarget : (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      2*(p.factorial : ℝ)*((2*b/c)*(1/(((i.val : ℝ)+1)*z)))^p*Real.exp (-gamma*x) := by
    have h1 := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ (p.factorial : ℝ)*((w n).rate i/W)^p by positivity)
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio p)
        (show 0 ≤ (p.factorial : ℝ) by positivity))
      (show 0 ≤ 2*Real.exp (-gamma*x) by positivity)
    exact (hm.trans (h1.trans h2)).trans_eq (by ring)
  have hd := uniform_moment_decay hp1 le_rfl (B := 2*b/c)
    (z := 1/(((i.val : ℝ)+1)*z)) (d := gamma) (x := x)
    (by positivity) (by positivity) hgamma.le (by dsimp [x]; positivity)
  apply deleted_kernel_eLpNorm_le_of_moment (w n) removed i q.val p (by omega) (by positivity)
  apply htarget.trans
  convert hd using 1
  congr 1
  dsimp [K,x,z]
  ring

end Luce.Section6
