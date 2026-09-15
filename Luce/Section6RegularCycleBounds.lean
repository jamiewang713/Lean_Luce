import Luce.Section6Lemma67Definitions
import Luce.Section6DensityEnvelope
import Luce.Section6ExponentialProductDensity
import Luce.Section6FilteredCycleCount
import Luce.Section6InactiveBounds
import Luce.Section6RightRateFloor

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace Luce.Section6

theorem selected_root_count_le_vertices {n : ℕ} (p : Equiv.Perm (Fin n))
    (k : ℕ) (S : Finset (Fin n)) :
    selectedRootCycleCount p k S ≤ exactCycleVertexCount p (k+1) S := by
  classical
  have he : selectedRootCycleCount p k S =
      ((Section5.maximumCycleRoots p k).filter (fun v => v ∈ S)).card := by
    convert filtered_cycle_count_eq_root_count p k (fun v _ => v ∈ S) using 1 <;>
      apply congrArg Finset.card <;> ext c <;> simp [selectedRootCycleCount]
  rw [he]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hroot, hS⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hS, (Section5.mem_maximumCycleRoots_iff p k i).mp hroot |>.1⟩

/-- Bounded selected rates give a uniform bound for actual cycles rooted
in the selected set, without any restrictions on the other rates. -/
theorem selected_root_expectation_of_rates {n : ℕ} (w : Weights n)
    (k : ℕ) (S : Finset (Fin n)) {d M : ℝ} (hd : 0 < d) (hM : 0 < M)
    (hrates : ∀ i ∈ S, d ≤ w.rate i ∧ w.rate i ≤ M) :
    (∫ clocks, (selectedRootCycleCount (raceRankPermutation clocks) k S : ℝ)
      ∂exponentialRace w) ≤ (3 : ℝ)^(k+1)*(M/d) := by
  let h : ℝ → ℝ := fun t => (M/d)*(exponentialPDF d t).toReal
  have hpdf := exponentialPDF_toReal_integrable hd
  have hpdf0 (t : ℝ) : 0 ≤ (exponentialPDF d t).toReal := ENNReal.toReal_nonneg
  have hint : (∫ t, (exponentialPDF d t).toReal) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpdf0)
      hpdf.aestronglyMeasurable]
    have he (t : ℝ) : ENNReal.ofReal (exponentialPDF d t).toReal = exponentialPDF d t :=
      ENNReal.ofReal_toReal (by simp [exponentialPDF])
    simp_rw [he]
    rw [lintegral_exponentialPDF_eq_one hd, ENNReal.toReal_one]
  have hh : Integrable h := hpdf.const_mul (M/d)
  have hi : (∫ t, h t) = M/d := by
    rw [integral_const_mul, hint, mul_one]
  have hdom (i : Fin n) (hiS : i ∈ S) (t : ℝ) :
      exponentialPDF (w.rate i) t ≤ ENNReal.ofReal (h t) := by
    obtain ⟨hdi, hiM⟩ := hrates i hiS
    by_cases ht : 0 ≤ t
    · rw [exponentialPDF_of_nonneg ht]
      have he : h t = M * Real.exp (-(d*t)) := by
        dsimp [h]
        rw [exponentialPDF_of_nonneg ht,
          ENNReal.toReal_ofReal (mul_nonneg hd.le (Real.exp_pos _).le)]
        field_simp
      rw [he]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul hiM (Real.exp_le_exp.mpr (by nlinarith))
        (Real.exp_pos _).le hM.le
    · rw [exponentialPDF_of_neg (lt_of_not_ge ht)]
      exact bot_le
  letI : ∀ i : Fin n, IsProbabilityMeasure (volume.withDensity (exponentialPDF (w.rate i))) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  have hb := density_envelope_product (fun i => exponentialPDF (w.rate i)) S (k+1)
    (by omega) h (Filter.Eventually.of_forall (fun t => mul_nonneg (by positivity) (hpdf0 t)))
    hh (fun i hi => Filter.Eventually.of_forall (hdom i hi))
  rw [hi] at hb
  change (∫ clocks, (exactCycleVertexCount (raceRankPermutation clocks) (k+1) S : ℝ)
    ∂exponentialRace w) ≤ _ at hb
  apply le_trans _ hb
  have hmeas : Measurable (fun clocks : Fin n → ℝ =>
      (exactCycleVertexCount (raceRankPermutation clocks) (k+1) S : ℝ)) :=
    (measurable_of_countable (fun a : ℕ => (a : ℝ))).comp
      (measurable_race_permutation_statistic (fun p => exactCycleVertexCount p (k+1) S))
  have hInt : Integrable (fun clocks : Fin n → ℝ =>
      (exactCycleVertexCount (raceRankPermutation clocks) (k+1) S : ℝ)) (exponentialRace w) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable (S.card : ℝ)
    filter_upwards [] with clocks
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast exactCycleVertexCount_le (raceRankPermutation clocks) (k+1) S
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _)) hInt
  filter_upwards [] with clocks
  exact_mod_cast selected_root_count_le_vertices (raceRankPermutation clocks) k S

/-- This includes fixed middle intervals and all inactive endpoints.
The constant is uniform over every cycle length at most L. -/
theorem PowerProfile.off_active_root_expectation {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (L : ℕ) {eps : ℝ} (he : 0 < eps) (he1 : eps < 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n k : ℕ), k < L →
      (∫ clocks, (selectedRootCycleCount (raceRankPermutation clocks) k
        (offActiveLabels left right n eps) : ℝ) ∂exponentialRace (w n)) ≤ C := by
  classical
  obtain ⟨d, M, hd, hM, hb⟩ := hp.bounds_off_active
    (eps := eps/2) (by linarith) (by linarith)
  refine ⟨(3 : ℝ)^L*(M/d), by positivity, ?_⟩
  intro grid w hw n k hk
  apply (selected_root_expectation_of_rates (w n) k _ hd hM ?_).trans
  · exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)) (by positivity)
  · intro i hi
    obtain ⟨hl, hr⟩ := (Finset.mem_filter.mp hi).2
    rw [hw n i]
    apply hb _ (samplePoint_mem grid i)
    · intro ha
      have hs := samplePoint_ge_half_label grid i
      have := hl ha
      linarith
    · intro ha
      have hs := samplePoint_ge_half_label grid i.rev
      rw [samplePoint_rev] at hs
      have hdrev : (i.rev.val : ℝ)+1 = (cornerDistance .right i : ℝ) := by
        exact_mod_cast (show i.rev.val+1 = n-i.val by simp only [Fin.val_rev]; omega)
      rw [hdrev] at hs
      have := hr ha
      linarith

end Luce.Section6
