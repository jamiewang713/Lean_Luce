import Luce.Section6LocalCornerData
import Luce.Section6QuarterWindow
import Luce.Section6NormalizedLocalPointwise
import Luce.Section5FiniteTaylor

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Uniform good-event approximation for one actual insertion factor.
The event and its polynomial failure probability are constructed from
the profile. No moderation restriction is required for this pointwise step. -/
theorem PowerProfile.corner_pointwise_window {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray)
    (hw : SampledRates grid w f) (r : ℕ) (side : Corner)
    (hactive : (cornerBehavior left right side).active) :
    ∃ rho C J d delta M : ℝ, 0 < rho ∧ 0 < C ∧ 0 < J ∧ 0 < d ∧
      0 < delta ∧ delta ≤ 1 ∧ 1 ≤ M ∧
      ∀ n (i j : Fin n), M ≤ (cornerDistance side i : ℝ) → M ≤ (cornerDistance side j : ℝ) →
        (cornerDistance side i : ℝ)/(n : ℝ) < delta → (cornerDistance side j : ℝ)/(n : ℝ) < delta →
        ∀ removed : Finset (Fin n), removed.card ≤ r →
        ∀ k : Fin (Finset.univ \ removed).card,
          |localGapDepth side (Finset.univ \ removed).card k.val-(cornerDistance side j : ℝ)| ≤ r →
        let behavior := cornerBehavior left right side
        let H := localEnvelopeKernel side behavior d (cornerDistance side i) (cornerDistance side j)
        let K := localIdealKernel side behavior (cornerDistance side i) (cornerDistance side j)
        let err := (cornerDistance side j : ℝ)^(-(1/4 : ℝ))+
          crossDepthError rho n (cornerDistance side i) (cornerDistance side j)
        K ≤ C*H ∧ ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
          (exponentialRace (w n)).real Gᶜ ≤ J*(cornerDistance side j : ℝ)^(-(1/2 : ℝ)) ∧
          ∀ᵐ old ∂exponentialRace (w n), old ∈ G →
            let xi := raceNormalizedGaps (compactDeletedWeights (w n) removed) (compactDeletedClocks removed old) k
            (deletedGapKernel (w n) removed old i k.val).toReal ≤ C*H*xi ∧
            |(deletedGapKernel (w n) removed old i k.val).toReal-K*xi| ≤
              C*H*(err*xi+xi^2/(cornerDistance side j : ℝ)) := by
  obtain ⟨rho, A, da, Ma, hrho, hA, hda, _, _, hdet⟩ := hp.corner_cross_depth_relative_error grid w hw side hactive
  obtain ⟨a, V, J, u0, dw, Mw, ha, _, hV, hJ, hu0, _, hdw, _, hwin⟩ := hp.corner_joint_quantile_window side hactive
  obtain ⟨hg, hq⟩ := hp.local_corner_parameters_pos side hactive
  let gamma := localCornerExponent (cornerBehavior left right side)
  let q := localCornerQ side (cornerBehavior left right side)
  let D := A+V+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by dsimp [D]; linarith
  have hAD : A ≤ D := by dsimp [D]; linarith
  have hVD : V ≤ D := by dsimp [D]; linarith
  obtain ⟨ds, Ms, hds, _, hsmall⟩ := joint_power_error_small hrho hD (by norm_num : (0 : ℝ) < 1/32)
  obtain ⟨Mu, _, hquarter⟩ := quarter_window_cutoff ha hu0 hD (by norm_num : (0 : ℝ) < 1/32) r
  let M := 1+|Ma|+|Mw|+|Ms|+|Mu|
  have hM1 : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg Ma, abs_nonneg Mw, abs_nonneg Ms, abs_nonneg Mu]
  have hMa : Ma ≤ M := by dsimp [M]; linarith [le_abs_self Ma, abs_nonneg Mw, abs_nonneg Ms, abs_nonneg Mu]
  have hMw : Mw ≤ M := by dsimp [M]; linarith [le_abs_self Mw, abs_nonneg Ma, abs_nonneg Ms, abs_nonneg Mu]
  have hMs : Ms ≤ M := by dsimp [M]; linarith [le_abs_self Ms, abs_nonneg Ma, abs_nonneg Mw, abs_nonneg Mu]
  have hMu : Mu ≤ M := by dsimp [M]; linarith [le_abs_self Mu, abs_nonneg Ma, abs_nonneg Mw, abs_nonneg Ms]
  let C0 := 1+22*gamma*q+16*gamma^2*q
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hC0D : C0 ≤ C0*D := by nlinarith only [hD1, hC0]
  refine ⟨rho, C0*D, J, q/4, min 1 (min da (min dw ds)), M, hrho, mul_pos hC0 hD,
    hJ, by positivity, lt_min zero_lt_one (lt_min hda (lt_min hdw hds)), min_le_left _ _, hM1, ?_⟩
  intro n i j hi hj his hjs removed hr k hk
  dsimp only
  let h : ℝ := cornerDistance side j
  let src : ℝ := cornerDistance side i
  let t := cornerQuantileTime side (w n) (cornerDistance side j)
  let mu := (n : ℝ)*populationD (w n) 1 t
  let u := h^(-(1/4 : ℝ))
  let e := crossDepthError rho n src h
  let H := localEnvelopeKernel side (cornerBehavior left right side) (q/4) (cornerDistance side i) (cornerDistance side j)
  let K := localIdealKernel side (cornerBehavior left right side) (cornerDistance side i) (cornerDistance side j)
  let x := localCornerRatio side (cornerBehavior left right side) (cornerDistance side i) (cornerDistance side j)
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsrc : 0 < src := Nat.cast_pos.mpr (cornerDistance_positive side i)
  have hh : 0 < h := Nat.cast_pos.mpr (cornerDistance_positive side j)
  have hx : 0 < x := localCornerRatio_positive side _ (cornerDistance_positive side i) (cornerDistance_positive side j)
  simp only [lt_min_iff] at his hjs
  have hhn : cornerDistance side j < n := by exact_mod_cast (div_lt_one hnR).mp hjs.1
  have ht : 0 < t := cornerQuantileTime_positive side (w n) (cornerDistance_positive side j) hhn
  have hmu : 0 < mu := mul_pos hnR (populationD_pos hn (w n) 1 t)
  have hu : 0 < u := Real.rpow_pos_of_pos hh _
  have he : 0 ≤ e := crossDepthError_nonneg hnR hsrc hh
  have hqtr := hquarter h (hMu.trans hj)
  have hmax : max src h/(n : ℝ) < ds := by
    rw [← max_div_div_right hnR.le]
    exact max_lt his.2.2.2 hjs.2.2.2
  have hDe : D*e ≤ 1/32 := hsmall _ _ (by positivity) hmax (le_min (hMs.trans hi) (hMs.trans hj))
  have heps : 0 ≤ D*(u+e) := by positivity
  have hepsSmall : D*(u+e) ≤ 1/16 := by nlinarith only [hDe, hqtr.2.1]
  have hAE : A*e ≤ D*(u+e) :=
    (mul_le_mul_of_nonneg_right hAD he).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hu.le) hD.le)
  have huE : u ≤ D*(u+e) := by
    calc
      u = 1*u := (one_mul _).symm
      _ ≤ D*u := mul_le_mul_of_nonneg_right hD1 hu.le
      _ ≤ D*(u+e) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right he) hD.le
  have hVuE : V*u ≤ D*(u+e) :=
    (mul_le_mul_of_nonneg_right hVD hu.le).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right he) hD.le)
  have hdet' := hdet n i j (hMa.trans hi) (hMa.trans hj) his.2.1 hjs.2.1
  have hH : 0 ≤ H := (localEnvelopeKernel_positive side _ _ (cornerDistance_positive side i) (cornerDistance_positive side j)).le
  have hKbound : K ≤ (C0*D)*H := by
    have hk' := localIdealKernel_le_envelope side _ hg.le hq.le (cornerDistance_positive side i)
      (cornerDistance_positive side j) (show q/4 ≤ q by dsimp [q]; linarith)
    have hc : gamma*q ≤ C0*D := by
      apply le_trans _ hC0D
      dsimp [C0]
      nlinarith only [mul_pos hg hq, mul_nonneg (sq_nonneg gamma) hq.le]
    exact hk'.trans (mul_le_mul_of_nonneg_right hc hH)
  refine ⟨hKbound, ?_⟩
  let G := {old | |raceGapStart (compactDeletedClocks removed old) k/t-1| ≤ u ∧
    |raceGapRate (compactDeletedWeights (w n) removed) (compactDeletedClocks removed old) k/mu-1| ≤ V*u}
  have hG : MeasurableSet G := by
    apply MeasurableSet.inter
    · exact measurableSet_le (((measurable_raceGapStart k).comp (compactDeletedClocks_measurable removed)).div_const t |>.sub_const 1 |>.abs) measurable_const
    · exact measurableSet_le (((measurable_raceGapRate (compactDeletedWeights (w n) removed) k).comp
        (compactDeletedClocks_measurable removed)).div_const mu |>.sub_const 1 |>.abs) measurable_const
  have hprob := hwin grid w hw n (cornerDistance side j) r (cornerDistance_positive side j) hhn
    (hMw.trans hj) hjs.2.2.1 removed hr k hk u hu hqtr.1 hqtr.2.2
  have hcomp : Gᶜ = {old | u < |raceGapStart (compactDeletedClocks removed old) k/t-1| ∨
    V*u < |raceGapRate (compactDeletedWeights (w n) removed) (compactDeletedClocks removed old) k/mu-1|} := by
    ext old
    simp only [G, mem_compl_iff, mem_ofPred_eq, not_and_or, not_le]
  refine ⟨G, hG, ?_, ?_⟩
  · rw [hcomp]
    exact hprob.trans_eq (quarter_window_probability_scale hh)
  · filter_upwards [exponentialRace_injective_ae (w n), exponentialRace_nonnegative_background (w n)] with old hold hpos
    intro hgood
    have hgood' : |raceGapStart (compactDeletedClocks removed old) k/t-1| ≤ u ∧
      |raceGapRate (compactDeletedWeights (w n) removed) (compactDeletedClocks removed old) k/mu-1| ≤ V*u := hgood
    have hW : 0 < raceGapRate (compactDeletedWeights (w n) removed) (compactDeletedClocks removed old) k :=
      orderedRemainingRate_pos _ _ _
    have hxi := raceNormalizedGaps_nonneg (compactDeletedWeights (w n) removed)
      (compactDeletedClocks removed old) (compactDeletedClocks_injective removed old hold)
      (fun l => hpos (deletedClockLabel removed l)) k
    have hpoint := normalized_local_pointwise ((w n).positive i) ht hmu hW hq hg hh hx heps hepsSmall hxi
      (hdet'.1.trans hAE) (hdet'.2.trans hAE) (hgood'.1.trans huE) (hgood'.2.trans hVuE)
    rw [deletedGapKernel_eq_normalizedGapMass (w n) removed old hold hpos i k]
    have hHid : x/h*Real.exp (-(q*x/4)) = H := by
      dsimp [H, localEnvelopeKernel, x, h]
      congr 2
      ring
    have hKid : gamma*q*x/h*Real.exp (-(q*x)) = K := by
      dsimp [K, localIdealKernel, gamma, q, x, h]
      congr 2
      ring
    dsimp only at hpoint
    rw [hHid, hKid] at hpoint
    constructor
    · exact hpoint.2.2.1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC0D hH) hxi)
    · apply hpoint.2.2.2.trans
      have hrem : 0 ≤ (raceNormalizedGaps (compactDeletedWeights (w n) removed) (compactDeletedClocks removed old) k)^2/h := by positivity
      have hb := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hD1 hrem) (mul_nonneg hC0.le hH)
      dsimp only [u, e, h, src] at *
      nlinarith only [hb]

end Luce.Section6
