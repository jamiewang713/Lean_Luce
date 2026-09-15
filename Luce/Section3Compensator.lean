import Luce.Section3EmpiricalRace

/-!
# Quantitative survival replacement for Section 3

The shrinking-band and independent-indicator steps in the proof of
Proposition 3.2 (`fixed_points.tex`, lines 759–780). All probabilities are
under the actual exponential-clock laws. These are auxiliary lemmas, not a
claim that the full compensator convergence has been assembled.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- The paper's weak survival indicator, including equality at the threshold. -/
def survivalGe (t x : ℝ) : ℝ := if t ≤ x then 1 else 0

lemma measurable_survivalGe (t : ℝ) : Measurable (survivalGe t) :=
  measurable_const.ite measurableSet_Ici measurable_const

lemma survivalGe_mem_Icc (t x : ℝ) : survivalGe t x ∈ Icc (0 : ℝ) 1 := by
  unfold survivalGe
  split_ifs <;> norm_num

/-- The deterministic event containment in lines 763–765. -/
lemma survivalGe_sub_le_band {τ t x δ : ℝ} (hclose : |τ - t| ≤ δ) :
    |survivalGe τ x - survivalGe t x| ≤
      if |x - t| ≤ δ then 1 else 0 := by
  have hc := abs_le.mp hclose
  unfold survivalGe
  split_ifs <;> simp_all only [sub_self, abs_zero, sub_zero, abs_one,
    zero_sub, abs_neg, le_refl, zero_le_one] <;>
    (exfalso; rename_i h; apply h; rw [abs_le]; constructor <;> linarith)

/-- An explicit version of `sup (a² exp(-a t)) < ∞`, with no bound on a.
Used for both the shrinking-band estimate and the interior variance. -/
theorem rate_sq_survival_le {r s u : ℝ} (hr : 0 ≤ r) (hu : 0 < u)
    (hus : u ≤ s) : r ^ 2 * survivalKernel s r ≤ 4 / u ^ 2 := by
  have he : (u * r / 2) * Real.exp (-(u * r / 2)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hp : 0 ≤ (u * r / 2) * Real.exp (-(u * r / 2)) :=
    mul_nonneg (by positivity) (Real.exp_pos _).le
  have hsquare : ((u * r / 2) * Real.exp (-(u * r / 2))) ^ 2 ≤ 1 := by
    nlinarith
  have heq : Real.exp (-(u * r / 2)) ^ 2 = survivalKernel u r := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, heq] at hsquare
  have hbase : r ^ 2 * survivalKernel u r ≤ 4 / u ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left (survivalKernel_antitone_time hr hus)
    (sq_nonneg r)).trans hbase

lemma hasDerivAt_rateKernel_time (r s : ℝ) :
    HasDerivAt (fun t => rateKernel t r) (-r ^ 2 * survivalKernel s r) s := by
  have h := (((hasDerivAt_id s).mul_const (-r)).exp).const_mul r
  have hfun : (fun t => rateKernel t r) = (fun y => r * Real.exp (id y * -r)) := by
    funext t
    simp [rateKernel, survivalKernel, mul_neg, neg_mul]
  rw [hfun]
  apply h.congr_deriv
  simp only [survivalKernel, id_eq, one_mul, mul_neg, neg_mul]
  ring

/-- Time-Lipschitz estimate away from zero, with a rate-independent constant. -/
theorem abs_rateKernel_time_sub_le {r s t u : ℝ} (hr : 0 ≤ r) (hu : 0 < u)
    (hus : u ≤ s) (hut : u ≤ t) :
    |rateKernel s r - rateKernel t r| ≤ (4 / u ^ 2) * |s - t| := by
  have h := (convex_Ici u).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_rateKernel_time r x).hasDerivWithinAt)
    (fun x hx => (show ‖-r ^ 2 * survivalKernel x r‖ ≤ 4 / u ^ 2 from by
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg r),
        abs_of_pos (survivalKernel_pos x r)]
      exact rate_sq_survival_le hr hu hx)) hut hus
  simpa only [Real.norm_eq_abs] using h

/-- The weighted probability of a closed band is exactly a difference of
remaining-rate kernels. Atomlessness handles both band endpoints. -/
lemma weighted_exponential_band_eq {r t δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (ht : 0 ≤ t - δ) :
    r * (expMeasure r).real {x | |x - t| ≤ δ} =
      rateKernel (t - δ) r - rateKernel (t + δ) r := by
  let := isProbabilityMeasure_expMeasure hr
  have hset : {x : ℝ | |x - t| ≤ δ} = Ici (t - δ) \ Ioi (t + δ) := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_sdiff, mem_Ici, mem_Ioi, not_lt, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hsub : Ioi (t + δ) ⊆ Ici (t - δ) := by
    intro x hx
    change t + δ < x at hx
    change t - δ ≤ x
    linarith
  rw [hset, measureReal_sdiff hsub measurableSet_Ioi]
  simp only [measureReal_def, expMeasure_Ici hr ht,
    expMeasure_Ioi hr (show 0 ≤ t + δ by linarith),
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [rateKernel, survivalKernel]
  rw [show -(r * (t - δ)) = -(t - δ) * r by ring,
    show -(r * (t + δ)) = -(t + δ) * r by ring]
  ring

/-- The explicit shrinking-band estimate in lines 767–772. -/
theorem weighted_exponential_band_le {r t δ u : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (hu : 0 < u) (hut : u ≤ t - δ) :
    r * (expMeasure r).real {x | |x - t| ≤ δ} ≤ 8 * δ / u ^ 2 := by
  rw [weighted_exponential_band_eq hr hδ (hu.le.trans hut)]
  calc
    _ ≤ |rateKernel (t - δ) r - rateKernel (t + δ) r| := le_abs_self _
    _ ≤ (4 / u ^ 2) * |(t - δ) - (t + δ)| :=
      abs_rateKernel_time_sub_le hr.le hu hut (by linarith)
    _ = _ := by rw [abs_of_nonpos (by linarith)]; ring

/-- Summing the pathwise replacement bound. In the paper `c i` is
`g(i/n)/D(t_i)` and `a i` is the rate; there is no restriction on dependence
between the perturbed times and the clocks. -/
theorem survival_replacement_bound {ι : Type*} (s : Finset ι)
    (a c τ t E : ι → ℝ) {δ C : ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hc : ∀ i ∈ s, |c i| ≤ C)
    (hclose : ∀ i ∈ s, |τ i - t i| ≤ δ) :
    |(∑ i ∈ s, c i * a i * survivalGe (τ i) (E i)) -
      (∑ i ∈ s, c i * a i * survivalGe (t i) (E i))| ≤
      C * ∑ i ∈ s, a i * (if |E i - t i| ≤ δ then 1 else 0) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg (ha i hi)]
  have hb := survivalGe_sub_le_band (x := E i) (hclose i hi)
  calc
    |c i| * a i * |survivalGe (τ i) (E i) - survivalGe (t i) (E i)|
      ≤ |c i| * a i * (if |E i - t i| ≤ δ then 1 else 0) :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (ha i hi))
    _ ≤ C * (a i * (if |E i - t i| ≤ δ then 1 else 0)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hc i hi) (mul_nonneg (ha i hi)
        (by split_ifs <;> norm_num))

/-- Closed-band indicator used only as a dominating random variable. -/
def clockBand (t δ x : ℝ) : ℝ := if |x - t| ≤ δ then 1 else 0

lemma measurable_clockBand (t δ : ℝ) : Measurable (clockBand t δ) := by
  exact measurable_const.ite
    (measurableSet_le ((measurable_id.sub_const t).norm) measurable_const)
    measurable_const

lemma clockBand_mem_Icc (t δ x : ℝ) : clockBand t δ x ∈ Icc (0 : ℝ) 1 := by
  unfold clockBand
  split_ifs <;> norm_num

lemma integral_clockBand {r : ℝ} (_hr : 0 < r) (t δ : ℝ) :
    (∫ x, clockBand t δ x ∂expMeasure r) =
      (expMeasure r).real {x | |x - t| ≤ δ} := by
  have heq : clockBand t δ = {x : ℝ | |x - t| ≤ δ}.indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp [clockBand, Set.indicator_apply]
  rw [heq, integral_indicator_const]
  · simp
  · exact measurableSet_le ((measurable_id.sub_const t).norm) measurable_const

/-- The integrated shrinking-band bound on the actual product law. The
constant is uniform over all rates, all labels, and all row sizes. This is
the expectation estimate to which the proof applies Markov's inequality. -/
theorem integral_normalized_clockBand_le {n : ℕ} (w : Weights (n + 1))
    (s : Finset (Fin (n + 1))) (t : Fin (n + 1) → ℝ) {δ u : ℝ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (ht : ∀ i ∈ s, u ≤ t i - δ) :
    (∫ E, (∑ i ∈ s, w.rate i * clockBand (t i) δ (E i)) / (n + 1 : ℕ)
      ∂exponentialRace w) ≤ 8 * δ / u ^ 2 := by
  have hint (i : Fin (n + 1)) : Integrable
      (fun E : Fin (n + 1) → ℝ => w.rate i * clockBand (t i) δ (E i))
      (exponentialRace w) := by
    exact ((memLp_of_bounded (μ := exponentialRace w)
      (Eventually.of_forall fun E : Fin (n + 1) → ℝ => clockBand_mem_Icc (t i) δ (E i))
      ((measurable_clockBand (t i) δ).comp (measurable_pi_apply i)).aestronglyMeasurable
      2).integrable (by norm_num)).const_mul _
  rw [integral_div, integral_finsetSum s (fun i _ => hint i)]
  have hterm : ∀ i ∈ s,
      (∫ E, w.rate i * clockBand (t i) δ (E i) ∂exponentialRace w) ≤
        8 * δ / u ^ 2 := by
    intro i hi
    rw [integral_const_mul, exponentialRace_integral_eval w i _
      (measurable_clockBand (t i) δ), integral_clockBand (w.positive i)]
    exact weighted_exponential_band_le (w.positive i) hδ hu (ht i hi)
  have hcard : (s.card : ℝ) ≤ (n + 1 : ℕ) := by
    exact_mod_cast (show s.card ≤ n + 1 by simpa using s.card_le_univ)
  apply (div_le_iff₀ (show (0 : ℝ) < (n + 1 : ℕ) by positivity)).mpr
  calc
    _ ≤ ∑ _i ∈ s, 8 * δ / u ^ 2 := Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * (8 * δ / u ^ 2) := by simp
    _ ≤ (n + 1 : ℕ) * (8 * δ / u ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

lemma integral_survivalGe {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    (∫ x, survivalGe t x ∂expMeasure r) = survivalKernel t r := by
  have heq : survivalGe t = (Ici t).indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp [survivalGe, Set.indicator_apply]
  rw [heq, integral_indicator_const _ measurableSet_Ici]
  simp [measureReal_def, expMeasure_Ici hr ht, survivalKernel, mul_comm]
  exact (Real.exp_pos _).le

lemma memLp_weighted_survivalGe {n : ℕ} (w : Weights n) (i : Fin n) (c t : ℝ) :
    MemLp (fun E : Fin n → ℝ => c * w.rate i * survivalGe t (E i)) 2
      (exponentialRace w) := by
  exact (memLp_of_bounded
    (Eventually.of_forall fun E : Fin n → ℝ => survivalGe_mem_Icc t (E i))
    ((measurable_survivalGe t).comp (measurable_pi_apply i)).aestronglyMeasurable
    2).const_mul (c * w.rate i)

/-- The exact expectation that remains after replacing the indicators,
as displayed in lines 787–793. The time may vary with the label. -/
theorem integral_normalized_survivalGe {n : ℕ} (w : Weights n)
    (s : Finset (Fin n)) (c t : Fin n → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) :
    (∫ E, (∑ i ∈ s, c i * w.rate i * survivalGe (t i) (E i)) / n
      ∂exponentialRace w) = (∑ i ∈ s, c i * rateKernel (t i) (w.rate i)) / n := by
  rw [integral_div, integral_finsetSum s (fun i _ =>
    (memLp_weighted_survivalGe w i (c i) (t i)).integrable (by norm_num))]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, exponentialRace_integral_eval w i _
    (measurable_survivalGe (t i)), integral_survivalGe (w.positive i) (ht i hi)]
  unfold rateKernel
  ring

/-- A single deterministic-time weighted survival variable has bounded
second moment after a positive time cutoff. -/
lemma variance_weighted_survivalGe_le {n : ℕ} (w : Weights n) (i : Fin n)
    {c t C u : ℝ} (hc : |c| ≤ C) (hu : 0 < u) (ht : u ≤ t) :
    variance (fun E : Fin n → ℝ => c * w.rate i * survivalGe t (E i))
      (exponentialRace w) ≤ 4 * C ^ 2 / u ^ 2 := by
  have hsquare : (fun E : Fin n → ℝ => (c * w.rate i * survivalGe t (E i)) ^ 2) =
      (fun E => (c * w.rate i) ^ 2 * survivalGe t (E i)) := by
    funext E
    unfold survivalGe
    split_ifs <;> ring
  have hC : 0 ≤ C := (abs_nonneg c).trans hc
  have hcsq : c ^ 2 ≤ C ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg c) hC).mpr hc
  calc
    _ ≤ ∫ E, (c * w.rate i * survivalGe t (E i)) ^ 2 ∂exponentialRace w :=
      variance_le_expectation_sq (memLp_weighted_survivalGe w i c t).aestronglyMeasurable
    _ = (c * w.rate i) ^ 2 * survivalKernel t (w.rate i) := by
      rw [hsquare, integral_const_mul, exponentialRace_integral_eval w i _
        (measurable_survivalGe t), integral_survivalGe (w.positive i) (hu.le.trans ht)]
    _ = c ^ 2 * (w.rate i ^ 2 * survivalKernel t (w.rate i)) := by ring
    _ ≤ C ^ 2 * (4 / u ^ 2) := by
      apply mul_le_mul hcsq (rate_sq_survival_le (w.positive i).le hu ht)
      · exact mul_nonneg (sq_nonneg _) (survivalKernel_pos _ _).le
      · positivity
    _ = _ := by ring

/-- The independent-indicator variance step in lines 776–780. The finite
set s represents ηn < k ≤ αn; the product law supplies independence. Neither
bounded rates nor identically distributed clocks are assumed. -/
theorem variance_normalized_survivalGe_le {n : ℕ} (w : Weights (n + 1))
    (s : Finset (Fin (n + 1))) (c t : Fin (n + 1) → ℝ) {C u : ℝ}
    (hc : ∀ i ∈ s, |c i| ≤ C) (hu : 0 < u) (ht : ∀ i ∈ s, u ≤ t i) :
    variance (fun E =>
      (∑ i ∈ s, c i * w.rate i * survivalGe (t i) (E i)) / (n + 1 : ℕ))
      (exponentialRace w) ≤ (4 * C ^ 2 / u ^ 2) / (n + 1 : ℕ) := by
  have hm (i : Fin (n + 1)) : Measurable
      (fun x => c i * w.rate i * survivalGe (t i) x) :=
    measurable_const.mul (measurable_survivalGe (t i))
  have hind := (exponentialRace_independent w).comp
    (fun i x => c i * w.rate i * survivalGe (t i) x) hm
  have hsumvar := IndepFun.variance_sum (s := s)
    (fun i _ => memLp_weighted_survivalGe w i (c i) (t i))
    (fun i _ j _ hij => hind.indepFun hij)
  have heq : (fun E : Fin (n + 1) → ℝ =>
      (∑ i ∈ s, c i * w.rate i * survivalGe (t i) (E i)) / (n + 1 : ℕ)) =
      (fun E => ((n + 1 : ℕ) : ℝ)⁻¹ *
        (∑ i ∈ s, fun E : Fin (n + 1) → ℝ =>
          c i * w.rate i * survivalGe (t i) (E i)) E) := by
    funext E
    simp [div_eq_mul_inv, mul_comm]
  rw [heq, variance_const_mul, hsumvar]
  have hN : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hcard : (s.card : ℝ) ≤ (n + 1 : ℕ) := by
    exact_mod_cast (show s.card ≤ n + 1 by simpa using s.card_le_univ)
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ ^ 2 * (∑ _i ∈ s, 4 * C ^ 2 / u ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun i hi =>
        variance_weighted_survivalGe_le w i (hc i hi) hu (ht i hi)
    _ = ((n + 1 : ℕ) : ℝ)⁻¹ ^ 2 * ((s.card : ℝ) * (4 * C ^ 2 / u ^ 2)) := by simp
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ ^ 2 * ((n + 1 : ℕ) * (4 * C ^ 2 / u ^ 2)) := by
      gcongr
    _ = _ := by field_simp [hN.ne']

end Luce
