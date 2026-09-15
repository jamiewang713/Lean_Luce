import Luce.Section4EndpointShellTightness

/-! The endpoint expectation property used by the finite-mean Poisson proof.
This is an internal interface: the final exceptional-shell theorem derives it
from the manuscript's raw combined cost assumption. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Luce

def EndpointExpectationTightness (w : WeightArray) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    ∀ᶠ n : ℕ in atTop,
      (∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace (w n)) < η

theorem endpointExpectationTightness_of_shells {w : WeightArray}
    (h : Tendsto (fun J => limsup (fun n => nonnegativeTail (shellExpectationCost w) n J) atTop) atTop (𝓝 0)) :
    ∀ η : ℝ, 0 < η → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ᶠ n : ℕ in atTop,
        (∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace (w n)) < η := by
  intro η hη
  obtain ⟨J₀, hJ₀⟩ := (nonnegativeTail_limit_iff _).mp h
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


/-- Probability tightness follows from the proved expectation estimate. -/
theorem EndpointExpectationTightness.probability_tightness {w : WeightArray}
    (h : EndpointExpectationTightness w) :
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
    obtain ⟨α, _, hα, hest⟩ := h (b/2) (by linarith)
    filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hα).filter_mono inf_le_left] with β _ hβ
    have hevent : ∀ᶠ n : ℕ in atTop, p β n ≤ b/2 := by
      filter_upwards [hest] with n hn
      exact (tailFixedPointCount_probability_le_expectation (w n) β).trans
        ((tailExpectation_antitone w n hβ.le).trans hn.le)
    have hlim : limsup (p β) atTop ≤ b/2 :=
      limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun _ => measureReal_nonneg)) hevent
    exact hlim.trans_lt (by linarith)

/-- Convert a vanishing extended-nonnegative iterated limsup to its real
counterpart. Eventual row boundedness is obtained from the extended limit. -/
theorem real_iterated_limit_of_ennreal
    {ι : Type*} {l : Filter ι} (a : ι → ℕ → ℝ) (ha : ∀ i n, 0 ≤ a i n)
    (h : Tendsto (fun i => limsup (fun n => ENNReal.ofReal (a i n)) atTop) l (𝓝 0)) :
    Tendsto (fun i => limsup (a i) atTop) l (𝓝 (0 : ℝ)) := by
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at ht
  apply ht.congr'
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))] with i hi
  have hb : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (a i n) ≤ 1 :=
    (eventually_lt_of_limsup_lt hi).mono fun _ hn => hn.le
  have he := ENNReal.limsup_toReal_eq (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hb
  change (limsup (fun n => ENNReal.ofReal (a i n)) atTop).toReal = limsup (a i) atTop
  simpa only [ENNReal.toReal_ofReal (ha i _)] using he.symm

/-- The literal expectation limit as the spatial cutoff tends to one. -/
theorem EndpointExpectationTightness.expectation_limit {w : WeightArray}
    (h : EndpointExpectationTightness w) :
    Tendsto (fun α : ℝ => limsup (fun n : ℕ =>
      ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace (w n)) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply real_iterated_limit_of_ennreal _ (fun _ _ => integral_nonneg (fun _ => Nat.cast_nonneg _))
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := 1) (by norm_num) hε.ne'
  rw [mul_one] at hδε
  obtain ⟨α, _, hα, hest⟩ := h δ (by exact_mod_cast hδ)
  filter_upwards [(eventually_gt_nhds hα).filter_mono inf_le_left] with β hβ
  apply le_trans (limsup_le_of_le (by isBoundedDefault) ?_) hδε.le
  filter_upwards [hest] with n hn
  simpa only [ENNReal.ofReal_coe_nnreal] using
    ENNReal.ofReal_le_ofReal ((tailExpectation_antitone w n hβ.le).trans hn.le)

end Luce

