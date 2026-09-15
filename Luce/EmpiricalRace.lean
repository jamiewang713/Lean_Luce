import Luce.ExponentialFacts
import Luce.RaceConvergence
import Luce.ProfileRegularity

/-!
# Concentration of the exponential race

Empirical arrival and remaining-rate processes on the actual product law of
exponential clocks.  The remaining-rate convention in this file uses strict
survival (`t < clock`); it agrees almost surely with weak survival at every
fixed deterministic time.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

def arrivalAt (t x : ℝ) : ℝ := if x ≤ t then 1 else 0

lemma arrivalAt_mem_Icc (t x : ℝ) : arrivalAt t x ∈ Icc (0 : ℝ) 1 := by
  unfold arrivalAt
  split_ifs <;> norm_num

lemma measurable_arrivalAt (t : ℝ) : Measurable (arrivalAt t) :=
  measurable_const.ite measurableSet_Iic measurable_const

lemma arrivalAt_monotone (x : ℝ) : Monotone (fun t => arrivalAt t x) := by
  intro s t hst
  dsimp [arrivalAt]
  split_ifs <;> simp_all <;> linarith

lemma integral_arrivalAt {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    (∫ x, arrivalAt t x ∂expMeasure r) = 1 - survivalKernel t r := by
  letI := isProbabilityMeasure_expMeasure hr
  have heq : arrivalAt t = (Iic t).indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp [arrivalAt, Set.indicator_apply]
  rw [heq, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one,
    ← cdf_eq_real, cdf_expMeasure_eq hr, if_pos ht]
  simp [survivalKernel, mul_comm]

lemma exponentialRace_integral_eval {n : ℕ} (w : Weights n) (i : Fin n)
    (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ clocks, g (clocks i) ∂exponentialRace w) = ∫ x, g x ∂expMeasure (w.rate i) := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (w.rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (w.positive j)
  have hmap := (measurePreserving_eval (fun j => expMeasure (w.rate j)) i).map_eq
  have h := integral_map (μ := exponentialRace w) (measurable_pi_apply i).aemeasurable
    hg.aestronglyMeasurable
  rw [show Measure.map (fun clocks : Fin n → ℝ => clocks i) (exponentialRace w) =
    expMeasure (w.rate i) from hmap] at h
  exact h.symm

def empiricalArrival {n : ℕ} (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, arrivalAt t (clocks i)) / n

def empiricalRemaining {n : ℕ} (w : Weights n) (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, w.rate i * (1 - arrivalAt t (clocks i))) / n

def meanArrival {n : ℕ} (w : Weights n) (t : ℝ) : ℝ :=
  (∑ i, (1 - survivalKernel t (w.rate i))) / n

def meanRemaining {n : ℕ} (w : Weights n) (t : ℝ) : ℝ :=
  (∑ i, rateKernel t (w.rate i)) / n

lemma memLp_empiricalArrival {n : ℕ} (w : Weights n) (t : ℝ) :
    MemLp (fun clocks => empiricalArrival clocks t) 2 (exponentialRace w) := by
  have h : MemLp (fun clocks : Fin n → ℝ => ∑ i, arrivalAt t (clocks i)) 2
      (exponentialRace w) := by
    apply memLp_finsetSum
    intro i _
    exact memLp_of_bounded (Eventually.of_forall fun clocks : Fin n → ℝ => arrivalAt_mem_Icc t (clocks i))
      ((measurable_arrivalAt t).comp (measurable_pi_apply i)).aestronglyMeasurable _
  simpa [empiricalArrival, div_eq_mul_inv] using h.mul_const (n : ℝ)⁻¹

lemma memLp_empiricalRemaining {n : ℕ} (w : Weights n) (t : ℝ) :
    MemLp (fun clocks => empiricalRemaining w clocks t) 2 (exponentialRace w) := by
  have h : MemLp (fun clocks : Fin n → ℝ =>
      ∑ i, w.rate i * (1 - arrivalAt t (clocks i))) 2 (exponentialRace w) := by
    apply memLp_finsetSum
    intro i _
    apply MemLp.const_mul
    exact (memLp_const 1).sub (memLp_of_bounded
      (Eventually.of_forall fun clocks : Fin n → ℝ => arrivalAt_mem_Icc t (clocks i))
      ((measurable_arrivalAt t).comp (measurable_pi_apply i)).aestronglyMeasurable 2)
  simpa [empiricalRemaining, div_eq_mul_inv] using h.mul_const (n : ℝ)⁻¹

lemma integral_empiricalArrival {n : ℕ} (w : Weights n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ clocks, empiricalArrival clocks t ∂exponentialRace w) = meanArrival w t := by
  unfold empiricalArrival meanArrival
  rw [integral_div]
  rw [integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [exponentialRace_integral_eval w i _ (measurable_arrivalAt t),
      integral_arrivalAt (w.positive i) ht]
  · intro i _
    exact (memLp_of_bounded (μ := exponentialRace w)
      (Eventually.of_forall fun clocks : Fin n → ℝ => arrivalAt_mem_Icc t (clocks i))
      ((measurable_arrivalAt t).comp (measurable_pi_apply i)).aestronglyMeasurable 2).integrable
      (by norm_num)

lemma integral_empiricalRemaining {n : ℕ} (w : Weights n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ clocks, empiricalRemaining w clocks t ∂exponentialRace w) = meanRemaining w t := by
  have hi : ∀ i : Fin n, Integrable (fun clocks : Fin n → ℝ => arrivalAt t (clocks i))
      (exponentialRace w) := by
    intro i
    exact (memLp_of_bounded (μ := exponentialRace w)
      (Eventually.of_forall fun clocks : Fin n → ℝ => arrivalAt_mem_Icc t (clocks i))
      ((measurable_arrivalAt t).comp (measurable_pi_apply i)).aestronglyMeasurable 2).integrable
      (by norm_num)
  unfold empiricalRemaining meanRemaining
  have hiw : ∀ i : Fin n, Integrable (fun clocks : Fin n → ℝ =>
      w.rate i * (1 - arrivalAt t (clocks i))) (exponentialRace w) := by
    intro i
    exact ((integrable_const 1).sub (hi i)).const_mul (w.rate i)
  rw [integral_div, integral_finsetSum Finset.univ (fun i _ => hiw i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_sub (integrable_const 1) (hi i), integral_const]
  rw [exponentialRace_integral_eval w i _ (measurable_arrivalAt t),
    integral_arrivalAt (w.positive i) ht]
  simp [rateKernel]

lemma empiricalArrival_monotone {n : ℕ} (clocks : Fin n → ℝ) :
    Monotone (empiricalArrival clocks) := by
  intro s t hst
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => arrivalAt_monotone (clocks i) hst) (Nat.cast_nonneg _)

lemma empiricalRemaining_antitone {n : ℕ} (w : Weights n) (clocks : Fin n → ℝ) :
    Antitone (empiricalRemaining w clocks) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (arrivalAt_monotone (clocks i) hst) 1)
    (w.positive i).le

set_option maxHeartbeats 800000 in
lemma variance_empiricalArrival_le {n : ℕ} (w : Weights (n + 1)) (t : ℝ) :
    variance (fun clocks => empiricalArrival clocks t) (exponentialRace w) ≤
      1 / (n + 1 : ℕ) := by
  have hind := (exponentialRace_independent w).comp (fun _ => arrivalAt t)
    (fun _ => measurable_arrivalAt t)
  have hbounded : ∀ i : Fin (n + 1), ∀ᵐ clocks ∂exponentialRace w,
      arrivalAt t (clocks i) ∈ Icc (0 : ℝ) 1 :=
    fun i => Eventually.of_forall fun clocks => arrivalAt_mem_Icc t (clocks i)
  have hm : ∀ i : Fin (n + 1), Measurable (fun clocks : Fin (n + 1) → ℝ =>
      arrivalAt t (clocks i)) :=
    fun i => (measurable_arrivalAt t).comp (measurable_pi_apply i)
  change variance (fun clocks : Fin (n + 1) → ℝ =>
      (∑ i, arrivalAt t (clocks i)) / (n + 1 : ℕ)) (exponentialRace w) ≤ _
  apply variance_normalized_sum_le (μ := exponentialRace w) (N := (n + 1 : ℕ)) (M := 1)
    (Finset.univ : Finset (Fin (n + 1)))
    (fun i clocks => arrivalAt t (clocks i)) (fun _ => (1 : ℝ))
    (by positivity) (by intros; norm_num) (by intros; rfl) (by simp)
    (fun i _ => memLp_of_bounded (hbounded i) (hm i).aestronglyMeasurable 2)
    (fun i _ j _ hij => hind.indepFun hij)
  intro i _
  have h := variance_le_sq_of_bounded (hbounded i) (hm i).aemeasurable
  norm_num at h ⊢
  linarith

set_option maxHeartbeats 800000 in
lemma variance_empiricalRemaining_le {n : ℕ} (w : Weights (n + 1)) (t : ℝ) {M : ℝ}
    (hnorm : ∑ i, w.rate i = (n + 1 : ℕ)) (hmax : ∀ i, w.rate i ≤ M) :
    variance (fun clocks => empiricalRemaining w clocks t) (exponentialRace w) ≤
      M / (n + 1 : ℕ) := by
  have hm : ∀ i : Fin (n + 1), Measurable (fun x => w.rate i * (1 - arrivalAt t x)) :=
    fun i => measurable_const.mul (measurable_const.sub (measurable_arrivalAt t))
  have hmc : ∀ i : Fin (n + 1), Measurable (fun clocks : Fin (n + 1) → ℝ =>
      w.rate i * (1 - arrivalAt t (clocks i))) :=
    fun i => (hm i).comp (measurable_pi_apply i)
  have hind := (exponentialRace_independent w).comp
    (fun i x => w.rate i * (1 - arrivalAt t x)) hm
  have hbounded : ∀ i : Fin (n + 1), ∀ᵐ clocks ∂exponentialRace w,
      w.rate i * (1 - arrivalAt t (clocks i)) ∈ Icc (0 : ℝ) (w.rate i) := by
    intro i
    apply Eventually.of_forall
    intro clocks
    have h := arrivalAt_mem_Icc t (clocks i)
    have hw := (w.positive i).le
    constructor <;> nlinarith [h.1, h.2]
  change variance (fun clocks : Fin (n + 1) → ℝ =>
      (∑ i, w.rate i * (1 - arrivalAt t (clocks i))) / (n + 1 : ℕ)) (exponentialRace w) ≤ _
  apply variance_normalized_sum_le (μ := exponentialRace w) (N := (n + 1 : ℕ)) (M := M)
    (Finset.univ : Finset (Fin (n + 1)))
    (fun i clocks => w.rate i * (1 - arrivalAt t (clocks i))) w.rate
    (by positivity) (fun i _ => (w.positive i).le) (fun i _ => hmax i) hnorm
    (fun i _ => memLp_of_bounded (hbounded i) (hmc i).aestronglyMeasurable 2)
    (fun i _ j _ hij => hind.indepFun hij)
  intro i _
  have h := variance_le_sq_of_bounded (hbounded i) (hmc i).aemeasurable
  nlinarith [sq_nonneg (w.rate i)]

/-- The arrival half of the uniform race law, on the actual exponential
product measures. -/
theorem uniform_empiricalArrival {w : ∀ n, Weights (n + 1)} {F : ℝ → ℝ} {T : ℝ}
    (hF : ContinuousOn F (Icc 0 T))
    (hmean : ∀ t ∈ Icc 0 T, Tendsto (fun n => meanArrival (w n) t) atTop (𝓝 (F t))) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ t ∈ Icc 0 T, ε ≤ |empiricalArrival clocks t - F t|}) atTop (𝓝 0) := by
  apply monotone_uniform_convergence_in_probability
    (fun _ clocks => empiricalArrival_monotone clocks) hF
  intro t ht
  apply concentration_of_variance_tendsto_zero (fun n => memLp_empiricalArrival (w n) t)
  · apply squeeze_zero (fun _ => variance_nonneg _ _) (fun n => variance_empiricalArrival_le (w n) t)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · simpa only [integral_empiricalArrival _ ht.1] using hmean t ht

/-- The remaining-rate half of the uniform race law (strict survival). -/
theorem uniform_empiricalRemaining {w : ∀ n, Weights (n + 1)} {D : ℝ → ℝ} {T : ℝ}
    {M : ℕ → ℝ} (hD : ContinuousOn D (Icc 0 T))
    (hnorm : ∀ n, ∑ i, (w n).rate i = (n + 1 : ℕ))
    (hmax : ∀ n i, (w n).rate i ≤ M n)
    (hsmall : Tendsto (fun n => M n / (n + 1 : ℕ)) atTop (𝓝 0))
    (hmean : ∀ t ∈ Icc 0 T, Tendsto (fun n => meanRemaining (w n) t) atTop (𝓝 (D t))) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ t ∈ Icc 0 T, ε ≤ |empiricalRemaining (w n) clocks t - D t|})
      atTop (𝓝 0) := by
  apply antitone_uniform_convergence_in_probability
    (fun n clocks => empiricalRemaining_antitone (w n) clocks) hD
  intro t ht
  apply concentration_of_variance_tendsto_zero (fun n => memLp_empiricalRemaining (w n) t)
  · exact squeeze_zero (fun _ => variance_nonneg _ _)
      (fun n => variance_empiricalRemaining_le (w n) t (hnorm n) (hmax n)) hsmall
  · simpa only [integral_empiricalRemaining _ ht.1] using hmean t ht

/-- The paper's weak-survival convention. -/
def empiricalRemainingGe {n : ℕ} (w : Weights n) (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, if t ≤ clocks i then w.rate i else 0) / n

lemma empiricalRemainingGe_antitone {n : ℕ} (w : Weights n) (clocks : Fin n → ℝ) :
    Antitone (empiricalRemainingGe w clocks) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp_all <;> linarith [w.positive i]

lemma empiricalRemainingGe_ae_eq {n : ℕ} (w : Weights n) (t : ℝ) :
    (fun clocks => empiricalRemainingGe w clocks t) =ᵐ[exponentialRace w]
      (fun clocks => empiricalRemaining w clocks t) := by
  have hne : ∀ i : Fin n, ∀ᵐ clocks ∂exponentialRace w, clocks i ≠ t := by
    intro i
    have hz : exponentialRace w {clocks | clocks i = t} = 0 := by
      change exponentialRace w ((Function.eval i) ⁻¹' {t}) = 0
      rw [(exponentialRace_eval w i).measure_preimage
        (measurableSet_singleton t).nullMeasurableSet]
      simp
    simpa only [ae_iff, not_not] using hz
  filter_upwards [ae_all_iff.mpr hne] with clocks hclocks
  unfold empiricalRemainingGe empiricalRemaining
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : t ≤ clocks i
  · have hn : ¬clocks i ≤ t := fun hh => hclocks i (le_antisymm hh h)
    simp [h, hn, arrivalAt]
  · have hlt : clocks i < t := lt_of_not_ge h
    simp [h, hlt.le, arrivalAt]

/-- Uniform convergence for exactly the weak-survival process from
equation `eq:uniform-race`. -/
theorem uniform_empiricalRemainingGe {w : ∀ n, Weights (n + 1)} {D : ℝ → ℝ} {T : ℝ}
    {M : ℕ → ℝ} (hD : ContinuousOn D (Icc 0 T))
    (hnorm : ∀ n, ∑ i, (w n).rate i = (n + 1 : ℕ))
    (hmax : ∀ n i, (w n).rate i ≤ M n)
    (hsmall : Tendsto (fun n => M n / (n + 1 : ℕ)) atTop (𝓝 0))
    (hmean : ∀ t ∈ Icc 0 T, Tendsto (fun n => meanRemaining (w n) t) atTop (𝓝 (D t))) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ t ∈ Icc 0 T, ε ≤ |empiricalRemainingGe (w n) clocks t - D t|})
      atTop (𝓝 0) := by
  apply antitone_uniform_convergence_in_probability
    (fun n clocks => empiricalRemainingGe_antitone (w n) clocks) hD
  intro t ht
  have hp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ε ≤ |empiricalRemaining (w n) clocks t - D t|}) atTop (𝓝 0) := by
    apply concentration_of_variance_tendsto_zero (fun n => memLp_empiricalRemaining (w n) t)
    · exact squeeze_zero (fun _ => variance_nonneg _ _)
        (fun n => variance_empiricalRemaining_le (w n) t (hnorm n) (hmax n)) hsmall
    · simpa only [integral_empiricalRemaining _ ht.1] using hmean t ht
  intro ε hε
  convert hp ε hε using 1
  congr 1
  funext n
  apply measure_congr
  filter_upwards [empiricalRemainingGe_ae_eq (w n) t] with clocks hc
  change (ε ≤ |empiricalRemainingGe (w n) clocks t - D t|) =
    (ε ≤ |empiricalRemaining (w n) clocks t - D t|)
  rw [hc]

end Luce
