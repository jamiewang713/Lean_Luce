import Luce.Assumptions
import Luce.Profile
import Luce.ProfileRegularity

/-!
# The actual step profiles in the interior race law

The bridge from Assumption 1.1 to the deterministic estimates used in Section 3.
In particular, integrability of the limit and negligibility of the largest
weight are consequences, not additional assumptions.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal

namespace Luce

instance : IsFiniteMeasure profileMeasure := by
  unfold profileMeasure
  infer_instance

instance : IsProbabilityMeasure profileMeasure := by
  constructor
  simp [profileMeasure, Real.volume_Ioo]

/-- Open cells may replace the paper's half-open cells in integrals, because
the endpoints have Lebesgue measure zero. -/
def profileCell (n : ℕ) (i : Fin n) : Set ℝ :=
  Ioo ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)

lemma measurable_stepProfile (w : WeightArray) (n : ℕ) : Measurable (stepProfile w n) := by
  unfold stepProfile
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.ite (measurableSet_Ioc) measurable_const

lemma integrable_stepProfile (w : WeightArray) (n : ℕ) :
    Integrable (stepProfile w n) profileMeasure := by
  unfold stepProfile
  apply integrable_finsetSum
  intro i hi
  apply ((integrable_const ((w n).rate i) (μ := profileMeasure)).indicator
    (measurableSet_Ioc : MeasurableSet
      (Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)))).congr
  filter_upwards [] with x
  by_cases hx : (i.val : ℝ) / n < x ∧ x ≤ ((i.val : ℝ) + 1) / n
  · rw [Set.indicator_of_mem
      (s := Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)) hx, if_pos hx]
  · rw [Set.indicator_of_notMem
      (s := Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)) hx, if_neg hx]

lemma stepProfile_nonneg (w : WeightArray) (n : ℕ) (x : ℝ) :
    0 ≤ stepProfile w n x := by
  unfold stepProfile
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact (w n).positive i |>.le
  · exact le_rfl

lemma ProfileLimit.aestronglyMeasurable {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) : AEStronglyMeasurable f profileMeasure := by
  apply aestronglyMeasurable_iff_nullMeasurable_separable.mpr
  exact ⟨hf.1, Set.univ, TopologicalSpace.isSeparable_univ_iff.mpr inferInstance,
    Eventually.of_forall (fun _ => Set.mem_univ _)⟩

lemma ProfileLimit.ae_pos {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) : ∀ᵐ x ∂profileMeasure, 0 < f x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hf.2.1 x hx

lemma ProfileLimit.ae_nonneg {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) : ∀ᵐ x ∂profileMeasure, 0 ≤ f x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact (hf.2.1 x hx).le

/-- `L¹` convergence to a measurable limit forces its integrability.  The
finiteness is obtained from an actual finite error term, not from normalization. -/
lemma ProfileLimit.integrable {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) : Integrable f profileMeasure := by
  have herr : ∀ᶠ n in atTop,
      eLpNorm (fun x => stepProfile w n x - f x) 1 profileMeasure < 1 :=
    hf.2.2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  obtain ⟨n, hn⟩ := herr.exists
  have hsub : Integrable (fun x => stepProfile w n x - f x) profileMeasure := by
    apply memLp_one_iff_integrable.mp
    exact ⟨(measurable_stepProfile w n).aestronglyMeasurable.sub hf.aestronglyMeasurable,
      hn.trans (by norm_num)⟩
  have h := (integrable_stepProfile w n).sub hsub
  apply h.congr
  filter_upwards [] with x
  exact sub_sub_cancel (stepProfile w n x) (f x)

/-- The real integral form of precisely the existing extended `L¹` error.
All errors are integrable, so no totalized integral is being used. -/
lemma ProfileLimit.tendsto_integral_abs_sub {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) :
    Tendsto (fun n => ∫ x, |stepProfile w n x - f x| ∂profileMeasure) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hf.2.2
  simp only [Function.comp_def, ENNReal.toReal_zero] at h
  convert h using 1
  funext n
  rw [eLpNorm_one_eq_lintegral_enorm]
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using
    (integral_norm_eq_lintegral_enorm
      ((measurable_stepProfile w n).aestronglyMeasurable.sub hf.aestronglyMeasurable))

lemma profileCell_subset (n : ℕ) (i : Fin n) :
    profileCell n i ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (Fin.neZero i).out)
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  exact ⟨lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg _) hn.le) hx.1,
    hx.2.trans_le ((div_le_one hn).mpr hi)⟩

/-- Exact pointwise value on the paper's half-open cell, including its right endpoint. -/
lemma stepProfile_eq_of_mem_Ioc (w : WeightArray) (n : ℕ) (i : Fin n) {x : ℝ}
    (hx : x ∈ Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)) :
    stepProfile w n x = (w n).rate i := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (Fin.neZero i).out)
  unfold stepProfile
  rw [Finset.sum_eq_single i]
  · simp only [hx.1, hx.2, and_self, if_true]
  · intro j hj hji
    apply if_neg
    intro hjx
    have hne : j.val ≠ i.val := by intro h; exact hji (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hij | hij
    · have hv : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hij
      have hdiv := div_le_div_of_nonneg_right hv hn.le
      linarith [hx.1, hjx.2]
    · have hv : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
      have hdiv := div_le_div_of_nonneg_right hv hn.le
      linarith [hx.2, hjx.1]
  · simp

lemma stepProfile_eq_on_cell (w : WeightArray) (n : ℕ) (i : Fin n) {x : ℝ}
    (hx : x ∈ profileCell n i) : stepProfile w n x = (w n).rate i :=
  stepProfile_eq_of_mem_Ioc w n i ⟨hx.1, hx.2.le⟩

lemma profileMeasure_cell (n : ℕ) (i : Fin n) :
    profileMeasure (profileCell n i) = ENNReal.ofReal (1 / (n : ℝ)) := by
  rw [profileMeasure, Measure.restrict_apply
      (show MeasurableSet (profileCell n i) from measurableSet_Ioo),
    inter_eq_left.mpr (profileCell_subset n i)]
  simp only [profileCell, Real.volume_Ioo]
  congr 1
  ring

/-- The normalized weight is exactly the mass of its actual profile cell. -/
lemma integral_stepProfile_cell (w : WeightArray) (n : ℕ) (i : Fin n) :
    ∫ x in profileCell n i, stepProfile w n x ∂profileMeasure = (w n).rate i / n := by
  have hn : 0 ≤ (1 / (n : ℝ)) := by positivity
  calc
    ∫ x in profileCell n i, stepProfile w n x ∂profileMeasure =
        ∫ _x in profileCell n i, (w n).rate i ∂profileMeasure := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      exact stepProfile_eq_on_cell w n i hx
    _ = (w n).rate i / n := by
      rw [setIntegral_const, Measure.real, profileMeasure_cell, ENNReal.toReal_ofReal hn]
      simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Equation `eq:max-weight`, first in its stronger arbitrary-cell form.
The chosen label may depend on the row without any consistency condition. -/
theorem ProfileLimit.rate_div_tendsto_zero {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (i : ∀ n, Fin (n + 1)) :
    Tendsto (fun n => (w (n + 1)).rate (i n) / (n + 1 : ℕ)) atTop (𝓝 0) := by
  apply tendsto_normalized_weight_of_cells (μ := profileMeasure)
    (f := f) (fn := fun n => stepProfile w (n + 1))
    (cells := fun n => profileCell (n + 1) (i n))
    hf.integrable (fun n => integrable_stepProfile w (n + 1))
  · exact hf.tendsto_integral_abs_sub.comp (tendsto_add_atTop_nat 1)
  · simp only [profileMeasure_cell]
    simpa only [Nat.cast_add, Nat.cast_one, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro n
    exact (integral_stepProfile_cell w (n + 1) (i n)).symm

/-- Maximum rate in positive row `n+1`; the row shift removes only the
irrelevant empty initial row of the triangular array. -/
def rowMaxRate (w : WeightArray) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (n + 1) => (w (n + 1)).rate i)

lemma rate_le_rowMaxRate (w : WeightArray) (n : ℕ) (i : Fin (n + 1)) :
    (w (n + 1)).rate i ≤ rowMaxRate w n :=
  Finset.le_sup' (fun i : Fin (n + 1) => (w (n + 1)).rate i) (Finset.mem_univ i)

/-- The largest normalized rate tends to zero under precisely Assumption 1.1,
as asserted in `fixed_points.tex`, Section 3, equation `eq:max-weight`. -/
theorem ProfileLimit.max_weight_div_tendsto_zero {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) :
    Tendsto (fun n => rowMaxRate w n / (n + 1 : ℕ)) atTop (𝓝 0) := by
  have h : ∀ n, ∃ i : Fin (n + 1), rowMaxRate w n = (w (n + 1)).rate i := by
    intro n
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : Fin (n + 1) => (w (n + 1)).rate i)
    exact ⟨i, heq⟩
  choose i hi using h
  simpa only [hi] using hf.rate_div_tendsto_zero i

theorem ProfileAssumption.max_weight_div_tendsto_zero {w : WeightArray}
    (h : ProfileAssumption w) :
    Tendsto (fun n => rowMaxRate w n / (n + 1 : ℕ)) atTop (𝓝 0) := by
  obtain ⟨f, hf⟩ := h
  exact hf.max_weight_div_tendsto_zero

/-- The deterministic remaining-rate transform converges uniformly on all
nonnegative times directly from Assumption 1.1. -/
theorem ProfileLimit.uniform_profileD {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) :
    TendstoUniformlyOn (fun n => profileD profileMeasure (stepProfile w n))
      (profileD profileMeasure f) atTop (Ici 0) := by
  exact tendstoUniformlyOn_profileD hf.integrable (integrable_stepProfile w)
    hf.ae_nonneg (fun n => Eventually.of_forall (stepProfile_nonneg w n))
    hf.tendsto_integral_abs_sub

/-- The deterministic arrival transform converges uniformly on every finite
time interval directly from Assumption 1.1. -/
theorem ProfileLimit.uniform_profileF {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (T : ℝ) :
    TendstoUniformlyOn (fun n => profileF profileMeasure (stepProfile w n))
      (profileF profileMeasure f) atTop (Icc 0 T) := by
  exact tendstoUniformlyOn_profileF hf.integrable (integrable_stepProfile w)
    hf.ae_nonneg (fun n => Eventually.of_forall (stepProfile_nonneg w n))
    hf.tendsto_integral_abs_sub T

/-- The paper's half-open cells cover their stated domain.  This also checks
that the step-profile representation has no omitted positive-measure points. -/
lemma exists_profile_cell {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ∃ i : Fin n, x ∈ Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnx : 0 < x * (n : ℝ) := mul_pos hx.1 hn'
  let k : ℕ := ⌈x * (n : ℝ)⌉₊
  have hkpos : 0 < k := Nat.ceil_pos.mpr hnx
  have hk : k ≤ n := Nat.ceil_le.mpr (by nlinarith [hx.2])
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  refine ⟨⟨k - 1, by omega⟩, ?_, ?_⟩
  · apply (div_lt_iff₀ hn').mpr
    change ((k - 1 : ℕ) : ℝ) < x * (n : ℝ)
    rw [hkcast]
    have h := Nat.ceil_lt_add_one hnx.le
    change (k : ℝ) < x * (n : ℝ) + 1 at h
    linarith
  · apply (le_div_iff₀ hn').mpr
    change x * (n : ℝ) ≤ ((k - 1 : ℕ) : ℝ) + 1
    rw [hkcast]
    have h := Nat.le_ceil (x * (n : ℝ))
    change x * (n : ℝ) ≤ (k : ℝ) at h
    linarith

/-- Concrete normalized example: every rate is one in every row. -/
def section3UnitWeights : WeightArray := fun _ =>
  ⟨fun _ => 1, fun _ => zero_lt_one⟩

lemma section3UnitWeights_normalized : NormalizedWeights section3UnitWeights := by
  intro n hn
  simp [section3UnitWeights, Nat.ne_of_gt hn]

/-- The profile hypothesis has an explicit inhabitant.  The constant-one
profile of the constant-one weights converges exactly, apart from row zero. -/
theorem section3UnitWeights_profileLimit :
    ProfileLimit section3UnitWeights (fun _ => 1) := by
  refine ⟨measurable_const.nullMeasurable, (fun _ _ => zero_lt_one), ?_⟩
  apply (tendsto_add_atTop_iff_nat 1).mp
  have heq (n : ℕ) :
      eLpNorm (fun x => stepProfile section3UnitWeights (n + 1) x - 1) 1
        profileMeasure = 0 := by
    apply eLpNorm_eq_zero_of_ae_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    obtain ⟨i, hi⟩ := exists_profile_cell (Nat.succ_pos n) ⟨hx.1, hx.2.le⟩
    rw [stepProfile_eq_of_mem_Ioc section3UnitWeights (n + 1) i hi]
    simp [section3UnitWeights]
  simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

end Luce
