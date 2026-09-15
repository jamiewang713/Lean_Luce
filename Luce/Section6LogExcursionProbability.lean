import Luce.Section6LogExcursionAlgebra
import Luce.Section6EndpointExcursionProbability
import Luce.Section6EndpointCycleProbability

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace Luce.Section6

theorem right_half_threshold67 {m R q : ℝ} (hm : 0 < m) (hR : 0 < R) :
    m^q/(R*m/2)^q = (2 : ℝ)^q*R^(-q) := by
  rw [Real.div_rpow (mul_pos hR hm).le (by norm_num),
    Real.mul_rpow hR.le hm.le, Real.rpow_neg hR.le]
  field_simp

theorem left_double_threshold67 {m R q : ℝ} (hm : 0 < m) (hR : 0 < R) :
    (1/m^q)/(1/(2*m/R)^q) = (2 : ℝ)^q*R^(-q) := by
  rw [Real.div_rpow (by positivity) hR.le,
    Real.mul_rpow (by norm_num) hm.le, Real.rpow_neg hR.le]
  field_simp

theorem PowerProfile.right_root_log_probability {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (k : ℕ) :
    ∃ C delta q : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < q ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (v : Fin n) (R : ℝ), 1 ≤ R →
      (cornerDistance .right v : ℝ)/(n : ℝ) ≤ delta →
      (exponentialRace (w n)).real (rootLogExcursionEvent .right k v R) ≤
        C/(cornerDistance .right v : ℝ)*R^(-q) := by
  obtain ⟨D, d, hD, hd, hd1, hroot⟩ := hp.right_cycle_vertex_probability k
  obtain ⟨K, q, e, hK, hq, he, he1, htail⟩ := hp.right_excursion_cycle_probability k
  refine ⟨(D+K)*2^q, min d e, q, by positivity, lt_min hd he,
    (min_le_left _ _).trans_lt hd1, hq, ?_⟩
  intro grid w hw n v R hR hv
  have hm : (0 : ℝ) < terminalDepth v := by exact_mod_cast terminalDepth_pos v
  have hRp : 0 < R := by linarith
  have hvd : (terminalDepth v : ℝ)/(n : ℝ) ≤ d := hv.trans (min_le_left _ _)
  have hve : (terminalDepth v : ℝ)/(n : ℝ) ≤ e := hv.trans (min_le_right _ _)
  have hcoef : D/(terminalDepth v : ℝ) ≤ (D+K)/(terminalDepth v : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  by_cases hR2 : R ≤ 2
  · have hb := hroot grid w hw n v hvd
    have hsub : (exponentialRace (w n)).real (rootLogExcursionEvent .right k v R) ≤
        (exponentialRace (w n)).real {clocks |
          minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro clocks hc
      exact ((Section5.mem_maximumCycleRoots_iff _ k v).mp hc.1).1
    have hfac := small_ratio_absorption67 hq hR hR2
    have ht := le_mul_of_one_le_right (show 0 ≤ D/(terminalDepth v : ℝ) by positivity) hfac
    have hu := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ (2 : ℝ)^q*R^(-q) by positivity)
    convert (hsub.trans hb).trans (ht.trans hu) using 1 <;>
      (first | rfl | (simp only [cornerDistance, terminalDepth]; ring) | ring)
  · have hB : (terminalDepth v : ℝ) ≤ R*(terminalDepth v : ℝ)/2 := by nlinarith
    have hb := htail grid w hw n v (R*(terminalDepth v : ℝ)/2) hB hve
    rw [right_half_threshold67 hm hRp] at hb
    have hsub : (exponentialRace (w n)).real (rootLogExcursionEvent .right k v R) ≤
        (exponentialRace (w n)).real {clocks |
          minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1 ∧
          ∃ z ∈ (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v).toFinset,
            R*(terminalDepth v : ℝ)/2 < (terminalDepth z : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro clocks hc
      obtain ⟨hperiod, hmax⟩ := (Section5.mem_maximumCycleRoots_iff _ k v).mp hc.1
      obtain ⟨z, hz, hlog⟩ := hc.2
      have hzv := hmax z hz
      have hmz : (terminalDepth v : ℝ) ≤ terminalDepth z := by
        exact_mod_cast (Nat.sub_le_sub_left hzv n)
      have hratio := log_distance_right_ratio hm hmz hRp hlog
      refine ⟨hperiod, z, hz, ?_⟩
      nlinarith [mul_pos hRp hm]
    have hu := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (show K ≤ D+K by linarith) hm.le)
      (show 0 ≤ (2 : ℝ)^q*R^(-q) by positivity)
    convert (hsub.trans hb).trans hu using 1 <;>
      (first | rfl | (simp only [cornerDistance, terminalDepth]; ring) | ring)

theorem PowerProfile.left_root_log_probability {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (k : ℕ) :
    ∃ C delta q : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < q ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (v : Fin n) (R : ℝ), 1 ≤ R →
      (cornerDistance .left v : ℝ)/(n : ℝ) ≤ delta →
      (exponentialRace (w n)).real (rootLogExcursionEvent .left k v R) ≤
        C/(cornerDistance .left v : ℝ)*R^(-q) := by
  obtain ⟨D, d, hD, hd, hd1, hroot⟩ := hp.left_cycle_vertex_probability k
  obtain ⟨K, q, e, hK, hq, he, he1, htail⟩ := hp.left_excursion_cycle_probability k
  refine ⟨(D+K)*2^q, min d e, q, by positivity, lt_min hd he,
    (min_le_left _ _).trans_lt hd1, hq, ?_⟩
  intro grid w hw n v R hR hv
  have hm : (0 : ℝ) < (v.val : ℝ)+1 := by positivity
  have hRp : 0 < R := by linarith
  have hdist : (cornerDistance .left v : ℝ) = (v.val : ℝ)+1 := by simp [cornerDistance]
  rw [hdist] at hv ⊢
  have hvd := hv.trans (min_le_left d e)
  have hve := hv.trans (min_le_right d e)
  by_cases hR2 : R ≤ 2
  · have hb := hroot grid w hw n v hvd
    have hsub : (exponentialRace (w n)).real (rootLogExcursionEvent .left k v R) ≤
        (exponentialRace (w n)).real {clocks |
          minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro clocks hc
      exact ((Section5.mem_maximumCycleRoots_iff _ k v).mp hc.1).1
    have ht := le_mul_of_one_le_right (show 0 ≤ D/((v.val : ℝ)+1) by positivity)
      (small_ratio_absorption67 hq hR hR2)
    have hu := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (show D ≤ D+K by linarith) hm.le)
      (show 0 ≤ (2 : ℝ)^q*R^(-q) by positivity)
    convert (hsub.trans hb).trans (ht.trans hu) using 1 <;> (first | rfl | ring)
  · have hA : 0 < 2*((v.val : ℝ)+1)/R := by positivity
    have hAm : 2*((v.val : ℝ)+1)/R ≤ (v.val : ℝ)+1 := by
      apply (div_le_iff₀ hRp).mpr
      nlinarith
    have hb := htail grid w hw n v (2*((v.val : ℝ)+1)/R) hA hAm hve
    rw [left_double_threshold67 hm hRp] at hb
    have hsub : (exponentialRace (w n)).real (rootLogExcursionEvent .left k v R) ≤
        (exponentialRace (w n)).real {clocks |
          minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1 ∧
          ∃ z ∈ (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v).toFinset,
            (z.val : ℝ)+1 < 2*((v.val : ℝ)+1)/R} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro clocks hc
      obtain ⟨hperiod, hmax⟩ := (Section5.mem_maximumCycleRoots_iff _ k v).mp hc.1
      obtain ⟨z, hz, hlog⟩ := hc.2
      have hzv := hmax z hz
      have hzm : (z.val : ℝ)+1 ≤ (v.val : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hzv 1
      have hzpos : (0 : ℝ) < (z.val : ℝ)+1 := by positivity
      simp only [cornerDistance, Nat.cast_add, Nat.cast_one] at hlog
      have hratio := log_distance_left_ratio hzpos hzm hRp hlog
      refine ⟨hperiod, z, hz, ?_⟩
      exact hratio.trans_lt (div_lt_div_of_pos_right (by linarith) hRp)
    have hu := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (show K ≤ D+K by linarith) hm.le)
      (show 0 ≤ (2 : ℝ)^q*R^(-q) by positivity)
    convert (hsub.trans hb).trans hu using 1 <;> (first | rfl | ring)

end Luce.Section6
