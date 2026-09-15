import Luce.Section4EndpointShellTailBridge
import Luce.Section4TailProbability

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Luce

/-- The actual spatial endpoint expectation estimate. All cutoff and
eventual-row choices are conclusions derived from the raw shell condition. -/
theorem EndpointShellAssumption.expectation_tightness {w : WeightArray}
    (h : EndpointShellAssumption w) (hnorm : NormalizedWeights w) :
    ∀ η : ℝ, 0 < η → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ᶠ n : ℕ in atTop,
        (∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace (w n)) < η := by
  intro η hη
  obtain ⟨J₀, hJ₀⟩ := (nonnegativeTail_limit_iff _).mp (h.expectation_shells hnorm)
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  let J := max 4096 J₀
  let q := Real.exp (-(J : ℝ))
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg J))
  refine ⟨1-q/2, by linarith, by linarith, ?_⟩
  filter_upwards [hJ₀, eventually_ge_atTop ⌈2/q⌉₊] with n hn hnlarge
  have hlarge : 2 ≤ (n : ℝ)*q := by
    have hn' : (⌈2/q⌉₊ : ℝ) ≤ n := by exact_mod_cast hnlarge
    have hceil := Nat.le_ceil (2/q)
    exact (div_le_iff₀ hq).mp (hceil.trans hn')
  apply (ENNReal.ofReal_lt_ofReal_iff hη).mp
  apply lt_of_le_of_lt (spatial_tail_expectation_le_shells w n J
    (by dsimp [J]; omega) hlarge)
  exact ((nonnegativeTail_antitone _ n (le_max_right 4096 J₀)).trans_lt hn)

theorem tailFixedPointCount_antitone {n : ℕ} (e : Fin n → ℝ) :
    Antitone (tailFixedPointCount e) := by
  classical
  intro α β hαβ
  apply Finset.card_le_card
  intro i hi
  simp only [tailFixedPointCount, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact ⟨lt_of_le_of_lt (mul_le_mul_of_nonneg_right hαβ (Nat.cast_nonneg n)) hi.1, hi.2⟩

theorem tailExpectation_antitone (w : WeightArray) (n : ℕ) :
    Antitone (fun α : ℝ => ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace (w n)) := by
  intro α β hαβ
  apply integral_mono (integrable_tailFixedPointCount (w n) β)
    (integrable_tailFixedPointCount (w n) α)
  intro e
  change (tailFixedPointCount e β : ℝ) ≤ (tailFixedPointCount e α : ℝ)
  exact_mod_cast tailFixedPointCount_antitone e hαβ

/-- Probability tightness follows from the proved expectation estimate. -/
theorem EndpointShellAssumption.probability_tightness {w : WeightArray}
    (h : EndpointShellAssumption w) (hnorm : NormalizedWeights w) :
    Tendsto (fun α : ℝ => limsup (fun n : ℕ =>
      (exponentialRace (w n)).real {e | 0 < tailFixedPointCount e α}) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let p := fun (α : ℝ) (n : ℕ) =>
    (exponentialRace (w n)).real {e | 0 < tailFixedPointCount e α}
  have hbounded (α : ℝ) : IsBoundedUnder (· ≤ ·) atTop (p α) :=
    ⟨1, show ∀ᶠ n : ℕ in atTop, p α n ≤ 1 from
      Eventually.of_forall fun _ => measureReal_le_one⟩
  have hnonneg (α : ℝ) : 0 ≤ limsup (p α) atTop :=
    le_limsup_of_frequently_le (Eventually.of_forall
      (fun _ => (measureReal_nonneg : 0 ≤ p α _))).frequently (hbounded α)
  apply (tendsto_order.2 ⟨?_, ?_⟩)
  · intro a ha
    exact Eventually.of_forall fun α => ha.trans_le (hnonneg α)
  · intro b hb
    obtain ⟨α, _, hα, hest⟩ := h.expectation_tightness hnorm (b/2) (by linarith)
    filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hα).filter_mono inf_le_left] with β _ hβ
    have hevent : ∀ᶠ n : ℕ in atTop, p β n ≤ b/2 := by
      filter_upwards [hest] with n hn
      exact (tailFixedPointCount_probability_le_expectation (w n) β).trans
        ((tailExpectation_antitone w n hβ.le).trans hn.le)
    have hlim : limsup (p β) atTop ≤ b/2 :=
      limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun _ => measureReal_nonneg)) hevent
    exact hlim.trans_lt (by linarith)

end Luce
