import Luce.Section6CriticalProbeBrackets
import Luce.Section6GapStartTail
import Luce.Section6LeftMeanEnvelope
import Luce.Section6SurvivalSplit

noncomputable section
open MeasureTheory
namespace Luce.Section6

/-- The arrival-tail error is absorbed into the rate-time exponential
because q/(i log(n/q)) is at most q in the critical corner. -/
theorem CriticalProfile.deleted_gap_survival {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ gamma Z : ℝ, 0 < gamma ∧ 1 ≤ Z ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card)
        (i : Fin n) (p : ℕ), 4 ≤ q.val → q.val ≤ n → 1 ≤ p →
        Z ≤ Real.log ((n : ℝ)/q.val) →
      (∫ e, Real.exp (-((p : ℝ)*(w n).rate i*raceGapStart (compactDeletedClocks removed e) q))
        ∂exponentialRace (w n)) ≤
      2*Real.exp (-gamma*((q.val : ℝ)/(((i.val : ℝ)+1)*Real.log ((n : ℝ)/q.val)))) := by
  obtain ⟨Z,hZ,hprobe⟩ := hp.probe_brackets
  obtain ⟨a,b,ha,hb,hrates⟩ := hp.sampled_global_comparison
  have hc : 0 < c := hp.2.2.1
  let gamma := min (a/(16*c)) (Real.log 2-1/2)
  have hg : 0 < gamma := lt_min (by positivity) log_two_sub_half_pos
  refine ⟨gamma,Z,hg,hZ,?_⟩
  intro grid w hw n removed q i p hq hqn hp1 hz
  let z := Real.log ((n : ℝ)/q.val)
  let x := (q.val : ℝ)/(((i.val : ℝ)+1)*z)
  let t := criticalProbeTime n q.val (1/(16*c))
  have hqp : (0 : ℝ) < q.val := by exact_mod_cast (show 0 < q.val by omega)
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hip : (0 : ℝ) < (i.val : ℝ)+1 := by positivity
  have hi1 : (1 : ℝ) ≤ (i.val : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have hz1 : 1 ≤ z := hZ.trans hz
  have hzp : 0 < z := by linarith
  have ht : 0 < t := by dsimp [t,criticalProbeTime]; positivity
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxq : x ≤ q.val := by
    dsimp [x]
    apply (div_le_iff₀ (mul_pos hip hzp)).mpr
    have hd := one_le_mul_of_one_le_of_one_le hi1 hz1
    nlinarith
  have hmean := (hprobe grid w hw n q.val hq hqn hz).1
  have hdel : (n : ℝ)*deletedG (w n) removed t ≤ (q.val : ℝ)/2 :=
    (mul_le_mul_of_nonneg_left (deletedG_le_populationG (w n) removed ht.le) hnp.le).trans hmean
  have htail := deleted_gap_start_tail_of_arrival_mean (w n) (by omega) removed q ht.le hdel
  have hrate : (a/(16*c))*x ≤ (w n).rate i*t := by
    have hh := mul_le_mul_of_nonneg_right (hrates grid w hw n i).1 ht.le
    apply le_trans _ hh
    dsimp [x,t,criticalProbeTime,z]
    field_simp
    exact le_rfl
  have hprt : gamma*x ≤ (p : ℝ)*(w n).rate i*t := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    have hh := mul_le_mul_of_nonneg_right (min_le_left (a/(16*c)) (Real.log 2-1/2)) hx
    have ht' : 0 < (w n).rate i*t := mul_pos ((w n).positive i) ht
    have hstep : (w n).rate i*t ≤ (p : ℝ)*(w n).rate i*t := by nlinarith
    exact hh.trans (hrate.trans hstep)
  have htail' : (exponentialRace (w n)).real {e | raceGapStart (compactDeletedClocks removed e) q < t} ≤
      Real.exp (-gamma*x) := by
    apply htail.trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_right (a/(16*c)) (Real.log 2-1/2)) hqp.le
    have hxg := mul_le_mul_of_nonneg_left hxq hg.le
    linarith
  have he0 : Real.exp (-((p : ℝ)*(w n).rate i*t)) ≤ Real.exp (-gamma*x) :=
    Real.exp_le_exp.mpr (by linarith)
  exact (deleted_survival_split (w n) removed i q p t).trans
    ((add_le_add he0 htail').trans_eq (by ring))

end Luce.Section6
