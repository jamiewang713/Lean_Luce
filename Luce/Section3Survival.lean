import Luce.Section3Replacement
import Luce.Section3Convergence
import Luce.Section3InitialBlock
import Luce.Section3OrderStats

/-!
# Survival replacement with the initial block removed

The lower time cutoff used in the stochastic estimates is derived here from
the manuscript's actual profile assumption and strict increase of the
inverse race distribution. No positive lower time assumption is retained.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal

namespace Luce

lemma initialRateMass_mono (w : WeightArray) (n : ℕ) :
    Monotone (initialRateMass w n) := by
  intro η ζ hηζ
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp_all <;> linarith [(w (n + 1)).positive i]

/-- Quantitative bound for discarding labels at or before η. -/
lemma normalized_sum_cutoff_error_le (w : WeightArray) (n : ℕ)
    (s : Finset (Fin (n + 1))) (X : Fin (n + 1) → ℝ) {η C : ℝ}
    (hC : 0 ≤ C) (hX : ∀ i ∈ s, |X i| ≤ C * (w (n + 1)).rate i) :
    |(∑ i ∈ s, X i) / (n + 1 : ℕ) -
      (∑ i ∈ s.filter (fun i => η < ((i.val : ℝ) + 1) / (n + 1 : ℕ)), X i) /
        (n + 1 : ℕ)| ≤ C * initialRateMass w n η := by
  classical
  have heq : (∑ i ∈ s, X i) -
      (∑ i ∈ s.filter (fun i => η < ((i.val : ℝ) + 1) / (n + 1 : ℕ)), X i) =
      ∑ i ∈ s, if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ η then X i else 0 := by
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all <;> linarith
  rw [← sub_div, heq, abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ (n + 1 : ℕ) by positivity)]
  have hsum : |∑ i ∈ s, if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ η then X i else 0| ≤
      C * ∑ i : Fin (n + 1), if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ η
        then (w (n + 1)).rate i else 0 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ i ∈ s, C * (if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ η then
            (w (n + 1)).rate i else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs <;> simp_all
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i _ _ => mul_nonneg hC (by split_ifs; exact ((w (n + 1)).positive i).le; rfl))
  have hdiv := div_le_div_of_nonneg_right hsum
    (show (0 : ℝ) ≤ (n + 1 : ℕ) by positivity)
  simpa only [initialRateMass, mul_div_assoc] using hdiv

lemma survivalGe_abs_sub_le_one (s t x : ℝ) : |survivalGe s x - survivalGe t x| ≤ 1 := by
  have hs := survivalGe_mem_Icc s x
  have ht := survivalGe_mem_Icc t x
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

lemma profileQuantile_pos_of_pos {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    0 < profileQuantile profileMeasure f η := by
  have h := strictMonoOn_profileQuantile hf.integrable hf.ae_pos
    (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hη.le, hη1⟩ hη
  rwa [profileQuantile_zero hf.integrable hf.ae_pos] at h

/-- Equation (replacement of survival indicators) for all selected interior
labels, under the actual profile hypothesis. The set s may be the full
interval k/n ≤ α or any of its subsets. -/
theorem section3_survival_replacement (w : WeightArray) (f : ℝ → ℝ)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (s : ∀ n, Finset (Fin (n + 1))) (c : ∀ n, Fin (n + 1) → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hs : ∀ n i, i ∈ s n → ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α)
    (hc : ∀ n i, i ∈ s n → |c n i| ≤ C) :
    ConvergesInProbability (fun n => exponentialRace (w (n + 1)))
      (fun n E =>
        ((∑ i ∈ s n, c n i * (w (n + 1)).rate i * survivalGe (orderTime E i) (E i)) -
          (∑ i ∈ s n, c n i * (w (n + 1)).rate i *
            survivalGe (profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ))) (E i))) /
          (n + 1 : ℕ)) 0 := by
  classical
  let t := fun n (i : Fin (n + 1)) =>
    profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ))
  let Z := fun n (E : Fin (n + 1) → ℝ) (i : Fin (n + 1)) =>
    c n i * (w (n + 1)).rate i * (survivalGe (orderTime E i) (E i) - survivalGe (t n i) (E i))
  have hZ : ∀ n E i, i ∈ s n → |Z n E i| ≤ C * (w (n + 1)).rate i := by
    intro n E i hi
    dsimp [Z]
    rw [abs_mul, abs_mul, abs_of_pos ((w (n + 1)).positive i)]
    calc
      _ ≤ |c n i| * (w (n + 1)).rate i * 1 :=
        mul_le_mul_of_nonneg_left (survivalGe_abs_sub_le_one (orderTime E i) (t n i) (E i))
          (mul_nonneg (abs_nonneg (c n i)) ((w (n + 1)).positive i).le)
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_right (hc n i hi) ((w (n + 1)).positive i).le
  have hconv : ConvergesInProbability (fun n => exponentialRace (w (n + 1)))
      (fun n E => (∑ i ∈ s n, Z n E i) / (n + 1 : ℕ)) 0 := by
    apply ConvergesInProbability.of_arbitrarily_close
    intro ε hε
    obtain ⟨η₀, hη₀, hmass⟩ := hf.initial_mass_small (show 0 < ε / (C + 1) by positivity)
    let η := min η₀ (1 / 2 : ℝ)
    have hη : 0 < η := lt_min hη₀ (by norm_num)
    have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
    let late := fun n => (s n).filter (fun i => η < ((i.val : ℝ) + 1) / (n + 1 : ℕ))
    have hlate : ∀ n i, i ∈ late n → i ∈ s n := fun _ _ hi => (Finset.mem_filter.mp hi).1
    have ht : ∀ n i, i ∈ late n → profileQuantile profileMeasure f η ≤ t n i := by
      intro n i hi
      exact (strictMonoOn_profileQuantile hf.integrable hf.ae_pos).monotoneOn
        ⟨hη.le, hη1⟩ ⟨by positivity, (hs n i (hlate n i hi)).trans_lt hα⟩
        (Finset.mem_filter.mp hi).2.le
    have hquantile : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
        (exponentialRace (w (n + 1))).real {E | ∃ i ∈ late n, δ < |orderTime E i - t n i|})
        atTop (𝓝 0) := by
      intro δ hδ
      have hl := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
        (section3_uniform_quantile w f hf hα δ hδ)
      apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa using hl)
      intro n
      apply measureReal_mono _ (measure_ne_top _ _)
      rintro E ⟨i, hi, hE⟩
      refine ⟨i, ?_, ?_⟩
      · simpa only [Nat.cast_add, Nat.cast_one] using hs n i (hlate n i hi)
      · simpa only [t, Nat.cast_add, Nat.cast_one] using hE.le
    have hlateconv := survival_replacement_converges (fun n => w (n + 1)) late c t
      (fun _ => orderTime) hC (fun n i hi => hc n i (hlate n i hi))
      (profileQuantile_pos_of_pos hf hη hη1) ht hquantile
    refine ⟨(fun n E => (∑ i ∈ late n, Z n E i) / (n + 1 : ℕ)), ?_, ?_⟩
    · simpa only [Z, mul_sub, Finset.sum_sub_distrib] using hlateconv
    · filter_upwards [hmass] with n hn E
      have hb := normalized_sum_cutoff_error_le w n (s n) (Z n E) (η := η) hC (hZ n E)
      have hmass' := (initialRateMass_mono w n (min_le_left η₀ (1 / 2 : ℝ))).trans hn.le
      have hcoef : C * (ε / (C + 1)) ≤ ε := by
        rw [show C * (ε / (C + 1)) = C * ε / (C + 1) by ring]
        apply (div_le_iff₀ (show 0 < C + 1 by linarith)).mpr
        nlinarith
      exact hb.trans ((mul_le_mul_of_nonneg_left hmass' hC).trans hcoef)
  simpa only [Z, t, mul_sub, Finset.sum_sub_distrib] using hconv

/-- The full interior deterministic-survival fluctuation, with its exact
expectation subtracted. Small times are handled by the profile's initial
mass estimate, so no time cutoff is retained in the statement. -/
theorem section3_survival_fluctuation (w : WeightArray) (f : ℝ → ℝ)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (s : ∀ n, Finset (Fin (n + 1))) (c : ∀ n, Fin (n + 1) → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hs : ∀ n i, i ∈ s n → ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α)
    (hc : ∀ n i, i ∈ s n → |c n i| ≤ C) :
    ConvergesInProbability (fun n => exponentialRace (w (n + 1)))
      (fun n E =>
        (∑ i ∈ s n, c n i * (w (n + 1)).rate i *
          survivalGe (profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ))) (E i)) /
            (n + 1 : ℕ) -
          (∑ i ∈ s n, c n i *
            rateKernel (profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ)))
              ((w (n + 1)).rate i)) / (n + 1 : ℕ)) 0 := by
  classical
  let t := fun n (i : Fin (n + 1)) =>
    profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ))
  let Z := fun n (E : Fin (n + 1) → ℝ) (i : Fin (n + 1)) =>
    c n i * (w (n + 1)).rate i * survivalGe (t n i) (E i) -
      c n i * rateKernel (t n i) ((w (n + 1)).rate i)
  have hZ : ∀ n E i, i ∈ s n → |Z n E i| ≤ C * (w (n + 1)).rate i := by
    intro n E i hi
    have ht0 : 0 ≤ t n i := profileQuantile_nonneg hf.integrable hf.ae_pos
      ⟨by positivity, (hs n i hi).trans_lt hα⟩
    have hB := survivalGe_mem_Icc (t n i) (E i)
    have hk := survivalKernel_le_one ht0 ((w (n + 1)).positive i).le
    have hkp := survivalKernel_pos (t n i) ((w (n + 1)).rate i)
    have hdiff : |survivalGe (t n i) (E i) - survivalKernel (t n i) ((w (n + 1)).rate i)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hB.1, hB.2]
    have heq : Z n E i = c n i * (w (n + 1)).rate i *
        (survivalGe (t n i) (E i) - survivalKernel (t n i) ((w (n + 1)).rate i)) := by
      dsimp [Z, rateKernel]
      ring
    rw [heq, abs_mul, abs_mul, abs_of_pos ((w (n + 1)).positive i)]
    calc
      _ ≤ |c n i| * (w (n + 1)).rate i * 1 :=
        mul_le_mul_of_nonneg_left hdiff (mul_nonneg (abs_nonneg _) ((w (n + 1)).positive i).le)
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_right (hc n i hi) ((w (n + 1)).positive i).le
  have hconv : ConvergesInProbability (fun n => exponentialRace (w (n + 1)))
      (fun n E => (∑ i ∈ s n, Z n E i) / (n + 1 : ℕ)) 0 := by
    apply ConvergesInProbability.of_arbitrarily_close
    intro ε hε
    obtain ⟨η₀, hη₀, hmass⟩ := hf.initial_mass_small (show 0 < ε / (C + 1) by positivity)
    let η := min η₀ (1 / 2 : ℝ)
    have hη : 0 < η := lt_min hη₀ (by norm_num)
    have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
    let late := fun n => (s n).filter (fun i => η < ((i.val : ℝ) + 1) / (n + 1 : ℕ))
    have hlate : ∀ n i, i ∈ late n → i ∈ s n := fun _ _ hi => (Finset.mem_filter.mp hi).1
    have ht : ∀ n i, i ∈ late n → profileQuantile profileMeasure f η ≤ t n i := by
      intro n i hi
      exact (strictMonoOn_profileQuantile hf.integrable hf.ae_pos).monotoneOn
        ⟨hη.le, hη1⟩ ⟨by positivity, (hs n i (hlate n i hi)).trans_lt hα⟩
        (Finset.mem_filter.mp hi).2.le
    have hlateconv := deterministic_survival_fluctuation_converges (fun n => w (n + 1)) late c t
      (fun n i hi => hc n i (hlate n i hi)) (profileQuantile_pos_of_pos hf hη hη1) ht
    refine ⟨(fun n E => (∑ i ∈ late n, Z n E i) / (n + 1 : ℕ)), ?_, ?_⟩
    · simpa only [Z, Finset.sum_sub_distrib, sub_div] using hlateconv
    · filter_upwards [hmass] with n hn E
      have hb := normalized_sum_cutoff_error_le w n (s n) (Z n E) (η := η) hC (hZ n E)
      have hmass' := (initialRateMass_mono w n (min_le_left η₀ (1 / 2 : ℝ))).trans hn.le
      have hcoef : C * (ε / (C + 1)) ≤ ε := by
        rw [show C * (ε / (C + 1)) = C * ε / (C + 1) by ring]
        apply (div_le_iff₀ (show 0 < C + 1 by linarith)).mpr
        nlinarith
      exact hb.trans ((mul_le_mul_of_nonneg_left hmass' hC).trans hcoef)
  simpa only [Z, t, Finset.sum_sub_distrib, sub_div] using hconv

end Luce
