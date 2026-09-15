import Luce.Section6CornerPointwiseWindow
import Luce.Section6CornerInsertionMoment
import Luce.Section6JointNormalizedEstimate
import Luce.Section6FiniteCommonConstants
import Luce.Section6MarkedGapDisplacement
import Luce.Section6Proposition65Contract

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal
namespace Luce.Section6

/-- The summed local estimate for nonempty separated configurations.
All constants are obtained from the original profile and the fixed
number of marks. The empty case and interval consequence are closed in
the final contract module. -/
theorem PowerProfile.proposition65_sum {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray)
    (hw : SampledRates grid w f) (r : ℕ) :
    ∃ (h0 : ℕ) (delta d kappa C : ℝ), 1 ≤ h0 ∧ 0 < delta ∧ delta < 1 ∧
      0 < d ∧ 0 < kappa ∧ kappa ≤ 1/8 ∧ 0 < C ∧
      ∀ n s : ℕ, 0 < s → s ≤ r → ∀ (side : Fin s → Corner) (u j : Fin s → Fin n),
        Injective u → Injective j →
        (∀ e, (cornerBehavior left right (side e)).active) →
        (∀ e, h0 ≤ cornerDistance (side e) (u e) ∧ h0 ≤ cornerDistance (side e) (j e)) →
        (∀ e, (cornerDistance (side e) (u e) : ℝ) ≤ delta*(n : ℝ) ∧
          (cornerDistance (side e) (j e) : ℝ) ≤ delta*(n : ℝ)) →
        (∀ e, localCornerRatio (side e) (cornerBehavior left right (side e))
          (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e)) ≤
          (min (cornerDistance (side e) (u e) : ℝ) (cornerDistance (side e) (j e) : ℝ))^(1/16 : ℝ)) →
        (∀ e g, e ≠ g → 2*r < Nat.dist (j e).val (j g).val) →
        |(exponentialRace (w n)).real {clocks | MarkedRankCylinder u j clocks} -
          ∏ e, localIdealKernel (side e) (cornerBehavior left right (side e))
            (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e))| ≤
          C*(∏ e, localEnvelopeKernel (side e) (cornerBehavior left right (side e)) d
            (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e)))*
          (∑ e, localPowerError kappa n (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e))) := by
  classical
  let I := {side : Corner // (cornerBehavior left right side).active}
  letI : Fintype I := Fintype.ofFinite I
  haveI : Nonempty I := by
    rcases hp.2.2.2.2 with hl | hr
    · exact ⟨⟨.left, hl⟩⟩
    · exact ⟨⟨.right, hr⟩⟩
  choose rho Cp Jp dp ep Mp hrho hCp hJp hdp hep hep1 hMp hpoint using
    (fun z : I => hp.corner_pointwise_window grid w hw r z.val z.property)
  let p0 := 2*max 1 r
  have hp0 : 0 < p0 := by dsimp [p0]; omega
  choose Cm dm Mm em hCm hdm hMm hem hem1 hmom using
    (fun z : I => hp.corner_moderate_insertion_moment r p0 hp0 (1/16)
      (by norm_num) (by norm_num) z.val z.property)
  obtain ⟨rho0, hrho0, hrholower⟩ := finite_positive_lower_bound rho hrho
  obtain ⟨d0, hd0, hdlower⟩ := finite_positive_lower_bound (fun z => min (dp z) (dm z))
    (fun z => lt_min (hdp z) (hdm z))
  obtain ⟨delta0, hdelta0, hcutlower⟩ := finite_positive_lower_bound (fun z => min (ep z) (em z))
    (fun z => lt_min (hep z) (hem z))
  let d := d0/2
  have hd : 0 < d := half_pos hd0
  have hdpoint (z : I) : d ≤ dp z :=
    (half_le_self hd0.le).trans ((hdlower z).trans (min_le_left _ _))
  have hdmoment (z : I) : d ≤ dm z :=
    (half_le_self hd0.le).trans ((hdlower z).trans (min_le_right _ _))
  let delta := min (1/4) (delta0/2)
  have hdelta : 0 < delta := lt_min (by norm_num) (half_pos hdelta0)
  have hdeltaquarter : delta ≤ 1/4 := min_le_left _ _
  have hdeltahalf : delta ≤ 1/2 := by linarith only [hdeltaquarter]
  have hdelta1 : delta < 1 := by linarith only [hdeltaquarter]
  have hcutpoint (z : I) : delta < ep z :=
    ((min_le_right _ _).trans_lt (half_lt_self hdelta0)).trans_le ((hcutlower z).trans (min_le_left _ _))
  have hcutmoment (z : I) : delta ≤ em z :=
    (min_le_right _ _).trans ((half_le_self hdelta0.le).trans ((hcutlower z).trans (min_le_right _ _)))
  let kappa := min (1/8) (rho0/2)
  have hk : 0 < kappa := lt_min (by norm_num) (half_pos hrho0)
  have hk8 : kappa ≤ 1/8 := min_le_left _ _
  have hk4 : kappa ≤ 1/4 := by linarith only [hk8]
  have hkrho (z : I) : kappa ≤ rho z :=
    (min_le_right _ _).trans ((half_le_self hrho0.le).trans (hrholower z))
  let C := 1+∑ z : I, (Cp z+Cm z)
  have hC1 : 1 ≤ C := by dsimp [C]; linarith [Finset.sum_nonneg (s := Finset.univ) (fun z _ => (add_pos (hCp z) (hCm z)).le)]
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hCpC (z : I) : Cp z ≤ C := (le_add_of_nonneg_right (hCm z).le).trans
    (finite_nonneg_le_one_add_sum _ (fun z => (add_pos (hCp z) (hCm z)).le) z)
  have hCmC (z : I) : Cm z ≤ C := (le_add_of_nonneg_left (hCp z).le).trans
    (finite_nonneg_le_one_add_sum _ (fun z => (add_pos (hCp z) (hCm z)).le) z)
  let J := 1+∑ z : I, Jp z
  have hJ : 0 < J := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun z _ => (hJp z).le))
  have hJpJ (z : I) : Jp z ≤ J := finite_nonneg_le_one_add_sum _ (fun z => (hJp z).le) z
  let M := 1+∑ z : I, (Mp z+|Mm z|)
  have hMp0 (z : I) : 0 ≤ Mp z := zero_le_one.trans (hMp z)
  have hMpoint (z : I) : Mp z ≤ M := (le_add_of_nonneg_right (abs_nonneg _)).trans
    (finite_nonneg_le_one_add_sum _ (fun z => add_nonneg (hMp0 z) (abs_nonneg _)) z)
  have hMmoment (z : I) : Mm z ≤ M := (le_abs_self _).trans ((le_add_of_nonneg_left (hMp0 z)).trans
    (finite_nonneg_le_one_add_sum _ (fun z => add_nonneg (hMp0 z) (abs_nonneg _)) z))
  let h0 := max (r+1) ⌈M⌉₊
  have hh0r : r+1 ≤ h0 := le_max_left _ _
  have hh01 : 1 ≤ h0 := by omega
  have hh01R : (1 : ℝ) ≤ h0 := by exact_mod_cast hh01
  have hMh0 : M ≤ (h0 : ℝ) := (Nat.le_ceil M).trans (Nat.cast_le.mpr (le_max_right _ _))
  let Csum := C^r*(4+(1+Real.sqrt ((2 : ℝ)^r))*Real.sqrt J)
  have hCsum : 0 < Csum := by dsimp [Csum]; positivity
  refine ⟨h0, delta, d, kappa, Csum, hh01, hdelta, hdelta1, hd, hk, hk8, hCsum, ?_⟩
  intro n s hs0 hsr side u j hu hj hactive hlarge hsmall hmoderate hsep
  have hn : 0 < n := Nat.zero_lt_of_lt (j ⟨0, hs0⟩).isLt
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let z : Fin s → I := fun e => ⟨side (Tuple.sort j e), hactive _⟩
  let removed := Finset.univ.image (u ∘ Tuple.sort j)
  have hremoved : removed.card ≤ r :=
    (Finset.card_image_le.trans (by simp : Finset.univ.card ≤ s)).trans hsr
  have hbuffer : ∀ e, r < n-(j e).val := fun e => endpoint_block_terminal_buffer hdeltahalf
    (side e) (j e) (hh0r.trans (hlarge e).2) (hsmall e).2
  let q : Fin s ↪ Fin (Finset.univ \ removed).card :=
    ⟨fun e => ⟨sortedMarkedGapIndex j e, sorted_gap_nonfinal_of_terminal_buffer hsr u j hu hj hbuffer e⟩,
      fun e g heq => sorted_gap_injective_of_separated hsr j hj hsep (congrArg Fin.val heq)⟩
  let src : Fin s → ℕ := fun e => cornerDistance (z e).val (u (Tuple.sort j e))
  let target : Fin s → ℕ := fun e => cornerDistance (z e).val (j (Tuple.sort j e))
  let K : Fin s → ℝ := fun e => localIdealKernel (z e).val (cornerBehavior left right (z e).val) (src e) (target e)
  let H : Fin s → ℝ := fun e => localEnvelopeKernel (z e).val (cornerBehavior left right (z e).val) d (src e) (target e)
  let E : Fin s → ℝ := fun e => localPowerError kappa n (src e) (target e)
  have hsrc (e : Fin s) : 0 < src e := cornerDistance_positive _ _
  have htarg (e : Fin s) : 0 < target e := cornerDistance_positive _ _
  have hsrcR (e : Fin s) : (0 : ℝ) < src e := Nat.cast_pos.mpr (hsrc e)
  have htargR (e : Fin s) : (0 : ℝ) < target e := Nat.cast_pos.mpr (htarg e)
  have hlargeR (e : Fin s) : (h0 : ℝ) ≤ src e ∧ (h0 : ℝ) ≤ target e :=
    ⟨Nat.cast_le.mpr (hlarge _).1, Nat.cast_le.mpr (hlarge _).2⟩
  have hsmallR (e : Fin s) : (src e : ℝ)/(n : ℝ) ≤ delta ∧ (target e : ℝ)/(n : ℝ) ≤ delta :=
    ⟨(div_le_iff₀ hnR).mpr (hsmall _).1, (div_le_iff₀ hnR).mpr (hsmall _).2⟩
  have hdepth (e : Fin s) : |localGapDepth (z e).val (Finset.univ \ removed).card (q e).val-(target e : ℝ)| ≤ r := by
    change |localGapDepth (side (Tuple.sort j e)) (Finset.univ \ removed).card (sortedMarkedGapIndex j e)-
      (cornerDistance (side (Tuple.sort j e)) (j (Tuple.sort j e)) : ℝ)| ≤ r
    cases he : side (Tuple.sort j e) with
    | left =>
      exact sorted_gap_left_displacement hsr j hj e
    | right =>
      exact sorted_gap_right_displacement hsr u j hu hj e
  have hpw (e : Fin s) := hpoint (z e) n (u (Tuple.sort j e)) (j (Tuple.sort j e))
    ((hMpoint _).trans (hMh0.trans (hlargeR e).1)) ((hMpoint _).trans (hMh0.trans (hlargeR e).2))
    ((hsmallR e).1.trans_lt (hcutpoint _)) ((hsmallR e).2.trans_lt (hcutpoint _)) removed hremoved (q e) (hdepth e)
  have hH (e : Fin s) : 0 ≤ H e := (localEnvelopeKernel_positive _ _ _ (hsrc e) (htarg e)).le
  have hK (e : Fin s) : 0 ≤ K e := localIdealKernel_nonneg _ _
    (hp.local_corner_parameters_pos (z e).val (z e).property).1.le
    (hp.local_corner_parameters_pos (z e).val (z e).property).2.le (hsrc e) (htarg e)
  have hE (e : Fin s) : 0 ≤ E e := localPowerError_nonneg hnR (hsrcR e) (htargR e)
  have hcoef (e : Fin s) : Cp (z e)*localEnvelopeKernel (z e).val (cornerBehavior left right (z e).val)
      (dp (z e)) (src e) (target e) ≤ C*H e :=
    mul_le_mul (hCpC _) (localEnvelopeKernel_antitone _ _ (hsrc e) (htarg e) (hdpoint _))
      (localEnvelopeKernel_positive _ _ _ (hsrc e) (htarg e)).le hC.le
  have hKB (e : Fin s) : K e ≤ C*H e := (hpw e).1.trans (hcoef e)
  have hpowers (e : Fin s) := local_error_powers hnR
    (hh01R.trans (hlargeR e).1) (hh01R.trans (hlargeR e).2)
    hk hk4 (hkrho (z e)) (show max (src e : ℝ) (target e : ℝ)/(n : ℝ) ≤ 1 by
      rw [← max_div_div_right hnR.le]
      exact (max_le (hsmallR e).1 (hsmallR e).2).trans hdelta1.le)
  have hlp (e : Fin s) : eLpNorm (fun old => (deletedGapKernel (w n) removed old (u (Tuple.sort j e)) (q e).val).toReal)
      ((2*s : ℕ) : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C*H e) := by
    have hshift : Nat.dist (q e).val (j (Tuple.sort j e)).val ≤ r+1 := by
      have hidx := sortedMarkedGapIndex_add j hj e
      have he := e.isLt
      change Nat.dist (sortedMarkedGapIndex j e) (j (Tuple.sort j e)).val ≤ r+1
      unfold Nat.dist
      omega
    have h := hmom (z e) grid w hw n (u (Tuple.sort j e)) (j (Tuple.sort j e))
      ((hMmoment _).trans (hMh0.trans (hlargeR e).1)) ((hMmoment _).trans (hMh0.trans (hlargeR e).2))
      ((hsmallR e).1.trans (hcutmoment _)) ((hsmallR e).2.trans (hcutmoment _)) removed hremoved (q e)
      (2*s) (by omega) (by dsimp [p0]; omega) hshift (hmoderate _)
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (hCmC _) (localEnvelopeKernel_antitone _ _ (hsrc e) (htarg e) (hdmoment _))
      (localEnvelopeKernel_positive _ _ _ (hsrc e) (htarg e)).le hC.le
  have hcontrol (e : Fin s) : ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (exponentialRace (w n)).real Gᶜ ≤ J*(target e : ℝ)^(-(1/2 : ℝ)) ∧
      ∀ᵐ old ∂exponentialRace (w n), old ∈ G →
        (deletedGapKernel (w n) removed old (u (Tuple.sort j e)) (q e).val).toReal ≤
          C*H e*markedNormalizedGaps (w n) removed q old e ∧
        |(deletedGapKernel (w n) removed old (u (Tuple.sort j e)) (q e).val).toReal-
          K e*markedNormalizedGaps (w n) removed q old e| ≤
          C*H e*((2*E e)*markedNormalizedGaps (w n) removed q old e+
            (markedNormalizedGaps (w n) removed q old e)^2/(target e : ℝ)) := by
    obtain ⟨G, hG, hprob, hgood⟩ := (hpw e).2
    refine ⟨G, hG, hprob.trans (mul_le_mul_of_nonneg_right (hJpJ _) (Real.rpow_nonneg (htargR e).le _)), ?_⟩
    filter_upwards [hgood, markedNormalizedGaps_nonneg_ae (w n) removed q] with old hold hxi
    intro hg
    have hb := hold hg
    constructor
    · exact hb.1.trans (mul_le_mul_of_nonneg_right (hcoef e) (hxi e))
    · apply hb.2.trans
      calc
        _ ≤ (Cp (z e)*localEnvelopeKernel (z e).val (cornerBehavior left right (z e).val)
            (dp (z e)) (src e) (target e))*
            ((2*E e)*markedNormalizedGaps (w n) removed q old e+
              (markedNormalizedGaps (w n) removed q old e)^2/(target e : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right (hpowers e).2.2 (hxi e)) le_rfl)
            (mul_nonneg (hCp _).le (localEnvelopeKernel_positive _ _ _ (hsrc e) (htarg e)).le)
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcoef e)
          (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hE e)) (hxi e)) (div_nonneg (sq_nonneg _) (htargR e).le))
  have hjoint := joint_normalized_estimate (w n) hs0 hsr removed (u ∘ Tuple.sort j) q K H E
    (fun e => (target e : ℝ)) hK hH hE htargR hC1 hJ.le hKB
    (fun e => (hpowers e).1) (fun e => (hpowers e).2.1) hlp hcontrol
  have hprobid := separated_cylinder_eq_gap_product (w n) hsr u j hu hj hsep
  simp only [ENNReal.toReal_prod] at hprobid
  change |(∫ old, ∏ e, (deletedGapKernel (w n) removed old (u (Tuple.sort j e)) (sortedMarkedGapIndex j e)).toReal
    ∂exponentialRace (w n))-(∏ e, K e)| ≤ Csum*(∏ e, H e)*(∑ e, E e) at hjoint
  rw [← hprobid] at hjoint
  have hPK : (∏ e, K e) = ∏ e, localIdealKernel (side e) (cornerBehavior left right (side e))
      (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e)) :=
    Equiv.prod_comp (Tuple.sort j) (fun e => localIdealKernel (side e) (cornerBehavior left right (side e))
      (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e)))
  have hPH : (∏ e, H e) = ∏ e, localEnvelopeKernel (side e) (cornerBehavior left right (side e)) d
      (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e)) :=
    Equiv.prod_comp (Tuple.sort j) (fun e => localEnvelopeKernel (side e) (cornerBehavior left right (side e)) d
      (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e)))
  have hSE : (∑ e, E e) = ∑ e, localPowerError kappa n (cornerDistance (side e) (u e))
      (cornerDistance (side e) (j e)) := Equiv.sum_comp (Tuple.sort j)
        (fun e => localPowerError kappa n (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e)))
  rwa [hPK, hPH, hSE] at hjoint

end Luce.Section6
