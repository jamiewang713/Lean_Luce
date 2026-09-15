import Luce.Section6CriticalHazardApproximation
import Luce.Section6SampledPowerExpansion

noncomputable section
open MeasureTheory
namespace Luce.Section6

/-- The actual predictable atoms admit the elementary deterministic
reference 1/(m log(n/m)), with an explicitly summable error. -/
theorem CriticalProfile.main_probability_approximation {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ K Z delta : ℝ, 0 < K ∧ 1 ≤ Z ∧ 0 < delta ∧ delta < 1 ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (k : Fin n), 4 ≤ k.val+1 → (n : ℝ) ≤ ((k.val : ℝ)+1)^2 →
      Z ≤ Real.log ((n : ℝ)/((k.val : ℝ)+1)) → ((k.val : ℝ)+1)/(n : ℝ) < delta →
      (∫ e, |predictableChance (w n) (raceRankPermutation e).symm k-
        1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))| ∂exponentialRace (w n)) ≤
      K/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))*
        ((1+Real.log (Real.log ((n : ℝ)/((k.val : ℝ)+1))))/
          Real.log ((n : ℝ)/((k.val : ℝ)+1))+1/((k.val : ℝ)+1)+
            (((k.val : ℝ)+1)/(n : ℝ))^eta) := by
  obtain ⟨K,Z,hK,hZ,hhazard⟩ := hp.hazard_approximation
  have hc : 0 < c := hp.2.2.1
  obtain ⟨C,delta,hC,hd,hd1,hprofile⟩ := hp.2.2.2.2.1.sampled_relative_error hc hp.2.2.2.1
  refine ⟨K+C,Z,delta,by positivity,hZ,hd,hd1,?_⟩
  intro grid w hw n k hk hnkm hz hdelta
  let m : ℝ := (k.val : ℝ)+1
  let z : ℝ := Real.log ((n : ℝ)/m)
  let r := (w n).rate k/(c*n*z)
  let q := 1/(m*z)
  let H := (1+Real.log z)/z+1/m
  have hm : 0 < m := by dsimp [m]; positivity
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.isLt)
  have hz1 : 1 ≤ z := hZ.trans hz
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hq : 0 < q := by dsimp [q]; positivity
  have herr := hprofile grid n k hdelta
  rw [← hw n k,Real.rpow_neg_one] at herr
  have hrq : |r-q| ≤ q*C*((m/n)^eta+1/m) := by
    have heq : r-q = q*((w n).rate k/(c*(m/n)⁻¹)-1) := by
      dsimp [r,q]
      field_simp
    rw [heq,abs_mul,abs_of_pos hq]
    exact (mul_le_mul_of_nonneg_left herr hq.le).trans_eq (by ring)
  have hP := integrable_race_permutation_statistic (w n)
    (fun π => |predictableChance (w n) π.symm k-q|)
  have hR := integrable_race_permutation_statistic (w n)
    (fun π => |predictableChance (w n) π.symm k-r|)
  have hi := integral_mono_ae hP (hR.add (integrable_const |r-q|))
    (Filter.Eventually.of_forall fun e => abs_sub_le (predictableChance (w n) (raceRankPermutation e).symm k) r q)
  simp only [Pi.add_apply] at hi
  rw [integral_add hR (integrable_const _),integral_const] at hi
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hi
  have hh := hhazard grid w hw n k hk hnkm hz
  have hh' : (∫ e, |predictableChance (w n) (raceRankPermutation e).symm k-r| ∂exponentialRace (w n)) ≤ K*q*H := by
    simpa only [r,q,H,m,z,div_eq_mul_inv,one_mul] using hh
  have hmain := hi.trans (add_le_add hh' hrq)
  have htarget : (K+C)/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))*
      ((1+Real.log (Real.log ((n : ℝ)/((k.val : ℝ)+1))))/
        Real.log ((n : ℝ)/((k.val : ℝ)+1))+1/((k.val : ℝ)+1)+(((k.val : ℝ)+1)/(n : ℝ))^eta) =
      (K+C)*q*(H+(m/n)^eta) := by dsimp [q,H,m,z]; ring
  rw [htarget]
  apply hmain.trans
  have hlog : 0 ≤ (1+Real.log z)/z := by have := Real.log_nonneg hz1; positivity
  have hpw : 0 ≤ (m/n)^eta := Real.rpow_nonneg (div_pos hm hn0).le _
  have h1 := mul_nonneg (mul_pos hK hq).le hpw
  have h2 := mul_nonneg (mul_pos hC hq).le hlog
  dsimp [H]
  ring_nf at h1 h2 ⊢
  linarith

end Luce.Section6
