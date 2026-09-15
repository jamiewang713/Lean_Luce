import Luce.Section3Profile

/-!
# The moderate-rate reservoir in Section 5

`fixed_points.tex`, lines 977–994, Lemma `lem:moderate-reservoir`.
The proof follows the source: positivity gives a large superlevel set, the
`L¹` error bounds its bad part, and the actual step-profile cells translate
Lebesgue measure into a count of labels. The last step subtracts the clocks
already removed. Normalization is not needed for this lemma.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal

namespace Luce

/-- The labels of rate at least `d`, counted with their original labels. -/
def moderateReservoir (w : WeightArray) (n : ℕ) (d : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => d ≤ (w n).rate i)

/-- Source lines 988–989: positive limiting rates have arbitrarily large
positive superlevel sets. All superlevel sets are measured on `(0,1)`. -/
lemma ProfileLimit.exists_large_superlevel {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {β : ℝ} (hβ : β < 1) :
    ∃ c : ℝ, 0 < c ∧ β < profileMeasure.real {x | c ≤ f x} := by
  let s : ℕ → Set ℝ := fun k => {x | 1 / ((k : ℝ) + 1) ≤ f x}
  have hs : Monotone s := by
    intro k l hkl x hx
    change 1 / ((l : ℝ) + 1) ≤ f x
    exact (Nat.one_div_le_one_div hkl).trans (show 1 / ((k : ℝ) + 1) ≤ f x from hx)
  have hu : profileMeasure (⋃ k, s k) = 1 := by
    calc
      profileMeasure (⋃ k, s k) = profileMeasure univ := by
        apply measure_congr
        filter_upwards [hf.ae_pos] with x hx
        change (x ∈ ⋃ k, s k) = (x ∈ univ)
        apply propext
        simp only [mem_iUnion, mem_univ, iff_true]
        have he : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < f x :=
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
            (gt_mem_nhds hx)
        obtain ⟨k, hk⟩ := he.exists
        exact ⟨k, hk.le⟩
      _ = 1 := measure_univ
  have ht := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp
    (show Tendsto (fun k => profileMeasure (s k)) atTop (𝓝 1) by
      simpa only [hu, Function.comp_def] using
        tendsto_measure_iUnion_atTop (μ := profileMeasure) hs)
  have he : ∀ᶠ k in atTop, β < profileMeasure.real (s k) :=
    (show Tendsto (fun k => profileMeasure.real (s k)) atTop (𝓝 1) by
      simpa only [Function.comp_def, ENNReal.toReal_one, Measure.real] using ht).eventually
      (lt_mem_nhds hβ)
  obtain ⟨k, hk⟩ := he.exists
  exact ⟨1 / ((k : ℝ) + 1), Nat.one_div_pos_of_nat, hk⟩

/-- The actual step-profile cells give the required counting multiplicity:
each labelled clock occupies one cell of length `1/n`. This upper bound needs
only the finite-union inequality; no disjointness restriction is dropped in
the opposite direction. -/
lemma stepProfile_superlevel_measure_le (w : WeightArray) {n : ℕ} (hn : 0 < n)
    (d : ℝ) :
    profileMeasure.real {x | d ≤ stepProfile w n x} ≤
      ((moderateReservoir w n d).card : ℝ) / n := by
  classical
  let cell : Fin n → Set ℝ := fun i =>
    Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)
  have heq : profileMeasure.real {x | d ≤ stepProfile w n x} =
      profileMeasure.real ({x | d ≤ stepProfile w n x} ∩ Ioo (0 : ℝ) 1) := by
    apply measureReal_congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    change (x ∈ {x | d ≤ stepProfile w n x}) =
      (x ∈ {x | d ≤ stepProfile w n x} ∩ Ioo (0 : ℝ) 1)
    apply propext
    simp only [mem_inter_iff, hx, and_true]
  rw [heq]
  have hsub : {x | d ≤ stepProfile w n x} ∩ Ioo (0 : ℝ) 1 ⊆
      ⋃ i ∈ moderateReservoir w n d, cell i := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_profile_cell hn ⟨hx.2.1, hx.2.2.le⟩
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨?_, hi⟩⟩
    simp only [moderateReservoir, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← stepProfile_eq_of_mem_Ioc w n i hi]
    exact hx.1
  have hc (i : Fin n) : profileMeasure.real (cell i) ≤ 1 / (n : ℝ) := by
    rw [profileMeasure, measureReal_restrict_apply measurableSet_Ioc]
    calc
      volume.real (cell i ∩ Ioo (0 : ℝ) 1) ≤ volume.real (cell i) :=
        measureReal_mono inter_subset_left (by simp [cell])
      _ = 1 / (n : ℝ) := by
        change volume.real (Ioc _ _) = _
        rw [Real.volume_real_Ioc_of_le]
        · ring
        · apply div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  calc
    _ ≤ profileMeasure.real (⋃ i ∈ moderateReservoir w n d, cell i) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ moderateReservoir w n d, profileMeasure.real (cell i) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ moderateReservoir w n d, 1 / (n : ℝ) :=
      Finset.sum_le_sum fun i _ => hc i
    _ = ((moderateReservoir w n d).card : ℝ) / n := by simp [div_eq_mul_inv]

/-- Source lines 987–992: the bad portion of a positive superlevel set is
controlled by the `L¹` error, and hence the reservoir contains linearly many
labels. The source allows every real `α < 1`, including negative `α`. -/
theorem ProfileLimit.moderate_reservoir {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ∃ d η : ℝ, 0 < d ∧ 0 < η ∧
      ∀ᶠ n : ℕ in atTop,
        (α + 2 * η) * (n : ℝ) ≤ ((moderateReservoir w n d).card : ℝ) := by
  let η : ℝ := (1 - α) / 8
  have hη : 0 < η := by dsimp [η]; linarith
  have hβ : α + 3 * η < 1 := by dsimp [η]; linarith
  obtain ⟨c, hc, hsuper⟩ := hf.exists_large_superlevel hβ
  let d := c / 2
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨d, η, hd, hη, ?_⟩
  have he : ∀ᶠ n in atTop,
      (∫ x, |stepProfile w n x - f x| ∂profileMeasure) < d * η :=
    hf.tendsto_integral_abs_sub.eventually (gt_mem_nhds (mul_pos hd hη))
  filter_upwards [he, eventually_gt_atTop 0] with n hn hnpos
  have hb : profileMeasure.real {x | d ≤ |stepProfile w n x - f x|} < η := by
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := profileMeasure) (Eventually.of_forall (fun x => abs_nonneg
        (stepProfile w n x - f x)))
      (((integrable_stepProfile w n).sub hf.integrable).abs) d
    nlinarith
  have hinc : {x | c ≤ f x} ⊆
      {x | d ≤ stepProfile w n x} ∪ {x | d ≤ |stepProfile w n x - f x|} := by
    intro x hx
    by_cases hx' : d ≤ stepProfile w n x
    · exact Or.inl hx'
    · right
      have habs := neg_le_abs (stepProfile w n x - f x)
      dsimp [d] at *
      change c ≤ f x at hx
      change c / 2 ≤ |stepProfile w n x - f x|
      linarith
  have hsum : profileMeasure.real {x | c ≤ f x} ≤
      profileMeasure.real {x | d ≤ stepProfile w n x} +
        profileMeasure.real {x | d ≤ |stepProfile w n x - f x|} :=
    (measureReal_mono hinc (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have hcount := stepProfile_superlevel_measure_le w hnpos d
  have hratio : α + 2 * η ≤ ((moderateReservoir w n d).card : ℝ) / n := by
    linarith
  exact (le_div_iff₀ (Nat.cast_pos.mpr hnpos)).mp hratio

/-- The finite counting step in source lines 992–994. `removed` includes
both deleted clocks and arrivals. Its arbitrary form makes the claimed
uniformity over all deletion/arrival configurations explicit. -/
lemma remaining_rate_of_reservoir (w : WeightArray) (n : ℕ)
    {α d η : ℝ} (hd : 0 ≤ d) (m : ℕ)
    (hcount : (α + 2 * η) * (n : ℝ) ≤ ((moderateReservoir w n d).card : ℝ))
    (hm : (m : ℝ) ≤ η * n) (removed : Finset (Fin n))
    (hremoved : (removed.card : ℝ) ≤ α * n + m) :
    d * η * n ≤ ∑ i ∈ Finset.univ \ removed, (w n).rate i := by
  classical
  have hcard : ((moderateReservoir w n d).card : ℝ) ≤
      ((moderateReservoir w n d \ removed).card : ℝ) + (removed.card : ℝ) := by
    exact_mod_cast Finset.card_le_card_sdiff_add_card
      (s := moderateReservoir w n d) (t := removed)
  have hleft : η * n ≤ ((moderateReservoir w n d \ removed).card : ℝ) := by
    nlinarith
  calc
    d * η * n ≤ d * ((moderateReservoir w n d \ removed).card : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hleft hd]
    _ = ∑ _i ∈ moderateReservoir w n d \ removed, d := by simp [mul_comm]
    _ ≤ ∑ i ∈ moderateReservoir w n d \ removed, (w n).rate i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2
    _ ≤ ∑ i ∈ Finset.univ \ removed, (w n).rate i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
      · intro i _ _
        exact (w n).positive i |>.le

/-- The full moderate-reservoir lemma, including its consequence after a
fixed number `m` of deletions and at most `α n` arrivals. The same constants
work for every fixed `m`; only the sufficiently-large-row threshold changes. -/
theorem ProfileLimit.moderate_reservoir_with_remaining_rate
    {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f)
    {α : ℝ} (hα : α < 1) :
    ∃ d η : ℝ, 0 < d ∧ 0 < η ∧
      (∀ᶠ n : ℕ in atTop,
        (α + 2 * η) * (n : ℝ) ≤ ((moderateReservoir w n d).card : ℝ)) ∧
      ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, ∀ removed : Finset (Fin n),
        (removed.card : ℝ) ≤ α * n + m →
          d * η * n ≤ ∑ i ∈ Finset.univ \ removed, (w n).rate i := by
  obtain ⟨d, η, hd, hη, hcount⟩ := hf.moderate_reservoir hα
  refine ⟨d, η, hd, hη, hcount, ?_⟩
  intro m
  have hm : ∀ᶠ n : ℕ in atTop, (m : ℝ) ≤ η * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop ((m : ℝ) / η))] with n hn
    have h := (div_le_iff₀ hη).mp hn
    linarith
  filter_upwards [hcount, hm] with n hn hmn
  exact remaining_rate_of_reservoir w n hd.le m hn hmn

/-- An explicit array satisfies all standing finite-mean hypotheses. Thus
the hypotheses used here, and the source's additional endpoint condition,
are jointly consistent. This is the manuscript's uniform-permutation example. -/
theorem section5UnitWeights_assumptions :
    NormalizedWeights section3UnitWeights ∧
      ProfileLimit section3UnitWeights (fun _ => 1) ∧
      EndpointAssumption section3UnitWeights := by
  refine ⟨section3UnitWeights_normalized, section3UnitWeights_profileLimit, ?_⟩
  refine ⟨1, 1, 0, zero_lt_one, zero_lt_one, ?_⟩
  intro n _ k _
  exact le_rfl

end Luce
