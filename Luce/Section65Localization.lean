import Luce.Section65LogWindows
import Luce.Section6Lemma67
import Luce.Section6SublinearCutoff
import Luce.Section5FiniteStatistic

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce.Section6

theorem excursionCount_le_logarithmic65 {n : ℕ} (hn : 2 ≤ n)
    (R : Equiv.Perm (Fin n)) (side : Corner) (k : ℕ) (a b δ : ℝ) :
    excursionCycleCount R side k a b δ ≤
      logarithmicExcursionCount R side k ((n : ℝ)^a) ((n : ℝ)^b) ((n : ℝ)^δ) := by
  classical
  unfold excursionCycleCount logarithmicExcursionCount
  apply Finset.card_le_card
  intro c hc
  obtain ⟨_,hc⟩ := Finset.mem_filter.mp hc
  have hw := (logLocation_window_iff65 hn side _ a b).mp ⟨hc.1,hc.2.1⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,hw.1.le,hw.2,?_⟩
  obtain ⟨v,hv,hvδ⟩ := hc.2.2
  refine ⟨v,hv,?_⟩
  rw [Real.log_rpow (by exact_mod_cast (show 0 < n by omega))]
  exact hvδ.le

theorem localization65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (side : Corner) (ha : (cornerBehavior left right side).active) (k : ℕ) {a b δ : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (hδ : 0 < δ) :
    Tendsto (fun n => ∫ clocks,
      (excursionCycleCount (raceRankPermutation clocks) side k a b δ : ℝ)
        ∂exponentialRace (w n)) atTop (𝓝 0) := by
  obtain ⟨C,d,q,hC,hd,hd1,hq,hest⟩ := lemma67_active f left right hp (k+1)
  have hlogbound := (hest k (by omega) side ha grid w hs).2.2
  obtain ⟨N,hN,hcut⟩ := sublinear_power_cutoff (ha0.trans hab) hb1 hd (H := 1)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (δ*q) (mul_pos hδ hq)).comp hlog
  have he1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (δ*q) (mul_pos hδ hq)).comp hlog
  simp only [Real.rpow_zero,one_mul] at he0
  simp only [Real.rpow_one] at he1
  have ht := (he0.add (he1.const_mul (b-a))).const_mul C
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => integral_nonneg (fun _ => by positivity))) _ ht
  filter_upwards [eventually_ge_atTop 2,tendsto_natCast_atTop_atTop.eventually_ge_atTop N]
    with n hn hnN
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hcutn := hcut n hnN
  have hbound := hlogbound n ((n : ℝ)^a) ((n : ℝ)^b) ((n : ℝ)^δ)
    (Real.one_le_rpow hn1 ha0.le) (Real.rpow_le_rpow_of_exponent_le hn1 hab.le)
    hcutn.2.2.le (Real.one_le_rpow hn1 hδ.le)
  have hmono : (∫ clocks, (excursionCycleCount (raceRankPermutation clocks) side k a b δ : ℝ)
      ∂exponentialRace (w n)) ≤
      ∫ clocks, (logarithmicExcursionCount (raceRankPermutation clocks) side k
        ((n : ℝ)^a) ((n : ℝ)^b) ((n : ℝ)^δ) : ℝ) ∂exponentialRace (w n) := by
    apply integral_mono (integrable_race_permutation_statistic (w n)
      (fun R => (excursionCycleCount R side k a b δ : ℝ)))
      (integrable_race_permutation_statistic (w n)
        (fun R => (logarithmicExcursionCount R side k ((n : ℝ)^a) ((n : ℝ)^b) ((n : ℝ)^δ) : ℝ)))
    intro clocks
    dsimp only
    exact_mod_cast excursionCount_le_logarithmic65 hn (raceRankPermutation clocks) side k a b δ
  apply (hmono.trans hbound).trans_eq
  rw [Real.log_div (Real.rpow_pos_of_pos hn0 b).ne' (Real.rpow_pos_of_pos hn0 a).ne',
    Real.log_rpow hn0,Real.log_rpow hn0,← Real.rpow_mul hn0.le,Real.rpow_def_of_pos hn0]
  simp only [Function.comp_apply]
  rw [show Real.log (n : ℝ)*(δ * -q) = -(δ*q)*Real.log (n : ℝ) by ring]
  ring

end Luce.Section6
