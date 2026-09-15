import Luce.Section5CyclicAnalytic
import Luce.Section5HighRates

/-!
# Truncation and finite-sum passage for Lemma 5.2

Source: `fixed_points.tex:1052–1075`. High-rate tuples are charged to one
marked source and all discarded restrictions are justified by nonnegativity.
For bounded rates, the geometric diagonals are null; the separated-grid
estimate is converted to an integral limit by dominated convergence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology BigOperators

namespace Luce

lemma prod_one_exception {r : ℕ} (a : Fin r) (H T : ℝ) :
    (∏ b : Fin r, if b = a then H else T) = H * T ^ (r - 1) := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), if_pos rfl]
  congr 1
  calc
    (∏ b ∈ Finset.univ.erase a, if b = a then H else T) =
        ∏ _b ∈ Finset.univ.erase a, T := by
      apply Finset.prod_congr rfl
      intro b hb
      exact if_neg (Finset.mem_erase.mp hb).1
    _ = T ^ (r - 1) := by simp

/-- The exact source mass in the high-rate union bound, with the coordinate
union counted at most r times and every other coordinate summed freely. -/
theorem sum_tuple_high_rate_le {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → Prop) [DecidablePred p] :
    (∑ i : Fin r → ι, if ∃ a, p (i a) then ∏ a, w (i a) else 0) ≤
      (r : ℝ) * (∑ k, if p k then w k else 0) * (∑ k, w k) ^ (r - 1) := by
  classical
  have hf (a : Fin r) (i : Fin r → ι) :
      (if p (i a) then ∏ b, w (i b) else 0) =
        ∏ b, if b = a then (if p (i b) then w (i b) else 0) else w (i b) := by
    by_cases hpa : p (i a)
    · rw [if_pos hpa]
      apply Finset.prod_congr rfl
      intro b _
      by_cases hba : b = a
      · subst b; simp [hpa]
      · simp only [if_neg hba]
    · rw [if_neg hpa]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      simp [hpa]
  have hsum (a : Fin r) :
      (∑ i : Fin r → ι, if p (i a) then ∏ b, w (i b) else 0) =
        (∑ k, if p k then w k else 0) * (∑ k, w k) ^ (r - 1) := by
    simp_rw [hf a]
    rw [← Fintype.prod_sum
      (fun b k => if b = a then (if p k then w k else 0) else w k)]
    convert prod_one_exception a (∑ k, if p k then w k else 0) (∑ k, w k) using 1
    apply Finset.prod_congr rfl
    intro b _
    by_cases hba : b = a <;> simp only [hba, if_true, if_false]
  calc
    _ ≤ ∑ i : Fin r → ι, ∑ a : Fin r, if p (i a) then ∏ b, w (i b) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      have hnonneg (a : Fin r) : 0 ≤ if p (i a) then ∏ b, w (i b) else 0 := by
        split_ifs
        · exact Finset.prod_nonneg (fun b _ => hw (i b))
        · exact le_rfl
      split_ifs with hi
      · obtain ⟨a, ha⟩ := hi
        simpa only [if_pos ha] using
          Finset.single_le_sum (fun b _ => hnonneg b) (Finset.mem_univ a)
      · exact Finset.sum_nonneg (fun a _ => hnonneg a)
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [hsum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Piecewise constant values on the actual multivariate profile cells. -/
def cyclicCellStep {r : ℕ} (n : ℕ) (b : (Fin r → Fin (n + 1)) → ℝ)
    (x : Fin r → ℝ) : ℝ :=
  ∑ i, (cyclicProfileCell n i).indicator (fun _ => b i) x

lemma cyclicCellStep_eq_of_mem {r n : ℕ} (b : (Fin r → Fin (n + 1)) → ℝ)
    {x : Fin r → ℝ} {i : Fin r → Fin (n + 1)} (hi : x ∈ cyclicProfileCell n i) :
    cyclicCellStep n b x = b i := by
  classical
  rw [cyclicCellStep, Finset.sum_eq_single i, Set.indicator_of_mem hi]
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (cyclicProfileCell_unique hj hi)) _
  · simp

lemma integrable_cyclicCellStep {r : ℕ} (n : ℕ) (b : (Fin r → Fin (n + 1)) → ℝ) :
    Integrable (cyclicCellStep n b) (cyclicProfileMeasure r) :=
  integrable_finsetSum Finset.univ (fun i _ =>
    (integrable_const (b i)).indicator (measurableSet_cyclicProfileCell n i))

lemma integral_cyclicCellStep {r : ℕ} (n : ℕ) (b : (Fin r → Fin (n + 1)) → ℝ) :
    (∫ x, cyclicCellStep n b x ∂cyclicProfileMeasure r) =
      (∑ i, b i) / (n + 1 : ℕ) ^ r := by
  simp only [cyclicCellStep]
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (measurableSet_cyclicProfileCell n _),
      cyclicProfileCell_real_measure, smul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  · intro i _
    exact (integrable_const (b i)).indicator (measurableSet_cyclicProfileCell n i)

lemma cyclicProfileMeasure_injective_ae (r : ℕ) :
    ∀ᵐ x ∂cyclicProfileMeasure r, Function.Injective x := by
  have : NullSingletonClass profileMeasure := by unfold profileMeasure; infer_instance
  have hpair (i j : Fin r) : ∀ᵐ x ∂cyclicProfileMeasure r, x i = x j → i = j := by
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ _ => hij)
    · have hi := (iIndepFun_pi (μ := fun _ : Fin r => profileMeasure)
        (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
      have hm := hi.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable
      rw [(measurePreserving_eval (fun _ : Fin r => profileMeasure) i).map_eq,
        (measurePreserving_eval (fun _ : Fin r => profileMeasure) j).map_eq] at hm
      have hz : cyclicProfileMeasure r {x | x i = x j} = 0 := by
        change (Measure.pi (fun _ : Fin r => profileMeasure))
          ((fun x => (x i, x j)) ⁻¹' Set.diagonal ℝ) = 0
        rw [← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
          measurableSet_diagonal, hm, Measure.prod_apply measurableSet_diagonal]
        simp [Set.diagonal]
      have hn : ∀ᵐ x ∂cyclicProfileMeasure r, x i ≠ x j := by
        rw [ae_iff]
        simpa only [not_not] using hz
      exact hn.mono (fun _ hne he => (hne he).elim)
  exact ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpair i))

/-- Every fixed distinct coordinate vector has eventually separated cell
endpoints. Thus the only vectors omitted by separated-rank asymptotics form
the proved null union of geometric diagonals. -/
lemma eventually_cyclic_grid_separated {r : ℕ} (hr : 0 < r) {x : Fin r → ℝ}
    (hx0 : ∀ a, 0 ≤ x a) (hinj : Function.Injective x) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ᶠ n in atTop, ∀ a b : Fin r, a ≠ b →
      ζ ≤ |profileGridEndpoint n (x a) - profileGridEndpoint n (x b)| := by
  classical
  let d : (Fin r × Fin r) → ℝ := fun ab => if ab.1 = ab.2 then 1 else |x ab.1 - x ab.2|
  have hs : (Finset.univ : Finset (Fin r × Fin r)).Nonempty :=
    ⟨(⟨0, hr⟩, ⟨0, hr⟩), Finset.mem_univ _⟩
  let δ := Finset.univ.inf' hs d
  have hδ : 0 < δ := by
    apply (Finset.lt_inf'_iff hs).mpr
    intro ab _
    dsimp [d]
    split_ifs with hab
    · norm_num
    · exact abs_pos.mpr (sub_ne_zero.mpr (fun he => hab (hinj he)))
  refine ⟨δ / 2, by positivity, eventually_all.mpr (fun a => eventually_all.mpr (fun b => ?_))⟩
  by_cases hab : a = b
  · exact Eventually.of_forall (fun _ hne => (hne hab).elim)
  · have hd : δ ≤ |x a - x b| := by
      simpa only [d, if_neg hab] using Finset.inf'_le d (Finset.mem_univ (a, b))
    have hlim := ((tendsto_profileGridEndpoint (hx0 a)).sub
      (tendsto_profileGridEndpoint (hx0 b))).abs
    have hl : δ / 2 < |x a - x b| := by linarith
    exact (hlim.eventually (lt_mem_nhds hl)).mono (fun n hn _ => hn.le)

/-- A uniformly bounded array whose separated-grid values tend uniformly to
zero has normalized sum tending to zero. The near-diagonal contribution is
removed by dominated convergence on the actual grid cells. -/
theorem tendsto_cyclic_array_sum_of_separated {r : ℕ} (hr : 0 < r)
    (A : (n : ℕ) → (Fin r → Fin (n + 1)) → ℝ) {B : ℝ}
    (hbound : ∀ᶠ n in atTop, ∀ i, |A n i| ≤ B)
    (hsep : ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i : Fin r → Fin (n + 1),
        (∀ a b : Fin r, a ≠ b →
          ζ ≤ |((i a).val + 1 : ℝ) / (n + 1 : ℕ) - ((i b).val + 1 : ℝ) / (n + 1 : ℕ)|) →
        |A n i| < ε) :
    Tendsto (fun n => (∑ i, A n i) / (n + 1 : ℕ) ^ r) atTop (𝓝 0) := by
  have hbase : ∀ᵐ y ∂profileMeasure, y ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  have hcoord := cyclic_ae_coordinates (r := r) hbase
  have hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (cyclicCellStep n (A n)) (cyclicProfileMeasure r) :=
    Eventually.of_forall (fun n => (integrable_cyclicCellStep n (A n)).1)
  have hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂cyclicProfileMeasure r,
      ‖cyclicCellStep n (A n) x‖ ≤ B := by
    filter_upwards [hbound] with n hn
    filter_upwards [hcoord] with x hx
    choose i hi using (fun a => exists_profile_cell (Nat.succ_pos n) ⟨(hx a).1, (hx a).2.le⟩)
    rw [cyclicCellStep_eq_of_mem (A n) (show x ∈ cyclicProfileCell n i from fun a _ => hi a)]
    exact hn i
  have hlim : ∀ᵐ x ∂cyclicProfileMeasure r,
      Tendsto (fun n => cyclicCellStep n (A n) x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hcoord, cyclicProfileMeasure_injective_ae r] with x hx hinj
    obtain ⟨ζ, hζ, hevent⟩ := eventually_cyclic_grid_separated hr (fun a => (hx a).1.le) hinj
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hevent, hsep ζ hζ ε hε] with n hn hAn
    choose i hi using (fun a => exists_profile_cell (Nat.succ_pos n) ⟨(hx a).1, (hx a).2.le⟩)
    rw [cyclicCellStep_eq_of_mem (A n) (show x ∈ cyclicProfileCell n i from fun a _ => hi a),
      Real.dist_eq, sub_zero]
    apply hAn i
    intro a b hab
    simpa only [profileGridEndpoint_of_mem_cell n (i a) (hi a),
      profileGridEndpoint_of_mem_cell n (i b) (hi b)] using hn a b hab
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : Fin r → ℝ => B)
    hmeas hdom (integrable_const B) hlim
  simpa only [integral_cyclicCellStep, integral_zero] using h

lemma ProfileLimit.eventually_rowMean_le {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ) ≤ C := by
  have hlim := tendsto_integral_of_L1' f hf.aestronglyMeasurable
    (Eventually.of_forall (integrable_stepProfile w)) hf.2.2
  have hm : Tendsto (fun n => (∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ))
      atTop (𝓝 (∫ y, f y ∂profileMeasure)) := by
    have he (n : ℕ) : (∫ x, stepProfile w (n + 1) x ∂profileMeasure) =
        (∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ) := by
      simpa only [id_eq] using integral_comp_stepProfile w (n + 1) id rfl
    have hlim2 := hlim.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n => ∫ x, stepProfile w (n + 1) x ∂profileMeasure) atTop
      (𝓝 (∫ y, f y ∂profileMeasure)) at hlim2
    simpa only [he] using hlim2
  refine ⟨max ((∫ y, f y ∂profileMeasure) + 1) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  filter_upwards [hm.eventually (gt_mem_nhds (lt_add_one _))] with n hn
  exact hn.le.trans (le_max_left _ _)

/-- Normalized high-rate product mass, exactly the expression in (1055–1058).
The source's distinctness and bulk restrictions may be dropped because every
summand on the right is nonnegative. -/
lemma normalized_tuple_high_rate_le {r : ℕ} (hr : 0 < r) (w : WeightArray)
    (n : ℕ) (M : ℝ) :
    (∑ i : Fin r → Fin (n + 1),
      if ∃ a, M < (w (n + 1)).rate (i a) then ∏ a, (w (n + 1)).rate (i a) else 0) /
        (n + 1 : ℕ) ^ r ≤
      (r : ℝ) * highRateMass w (n + 1) M *
        ((∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ)) ^ (r - 1) := by
  classical
  have h := div_le_div_of_nonneg_right
    (sum_tuple_high_rate_le (r := r) ((w (n + 1)).rate) (fun i => (w (n + 1)).positive i |>.le)
      (fun i => M < (w (n + 1)).rate i))
    (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ) ^ r)
  refine h.trans_eq ?_
  simp only [highRateMass, Finset.sum_filter]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : ((n + 1 : ℕ) : ℝ) ^ r = (n + 1 : ℕ) * (n + 1 : ℕ) ^ (r - 1) := by
    calc
      ((n + 1 : ℕ) : ℝ) ^ r = (n + 1 : ℕ) ^ ((r - 1) + 1) :=
        congrArg (fun k => ((n + 1 : ℕ) : ℝ) ^ k) (Nat.sub_add_cancel hr).symm
      _ = _ := by rw [pow_succ]; ring
  rw [div_pow, hpow]
  field_simp

lemma cyclic_array_truncation_error {r : ℕ} (hr : 0 < r) (w : WeightArray)
    (n : ℕ) (M : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (A : (Fin r → Fin (n + 1)) → ℝ)
    (hA : ∀ i, |A i| ≤ K * ∏ a, (w (n + 1)).rate (i a)) :
    |(∑ i, A i) / (n + 1 : ℕ) ^ r -
      (∑ i, if ∀ a, (w (n + 1)).rate (i a) ≤ M then A i else 0) / (n + 1 : ℕ) ^ r| ≤
      K * ((r : ℝ) * highRateMass w (n + 1) M *
        ((∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ)) ^ (r - 1)) := by
  classical
  rw [← sub_div, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ) ^ r)]
  have hsum : |(∑ i, A i) - ∑ i, if ∀ a, (w (n + 1)).rate (i a) ≤ M then A i else 0| ≤
      K * ∑ i : Fin r → Fin (n + 1),
        if ∃ a, M < (w (n + 1)).rate (i a) then ∏ a, (w (n + 1)).rate (i a) else 0 := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : ∀ a, (w (n + 1)).rate (i a) ≤ M
    · have hh : ¬∃ a, M < (w (n + 1)).rate (i a) := by simpa only [not_exists, not_lt] using hi
      simp only [if_pos hi, if_neg hh, sub_self, abs_zero, mul_zero, le_refl]
    · have hh : ∃ a, M < (w (n + 1)).rate (i a) := by simpa only [not_forall, not_le] using hi
      simpa only [if_neg hi, if_pos hh, sub_zero] using hA i
  calc
    _ ≤ (K * ∑ i : Fin r → Fin (n + 1),
        if ∃ a, M < (w (n + 1)).rate (i a) then ∏ a, (w (n + 1)).rate (i a) else 0) /
        (n + 1 : ℕ) ^ r := div_le_div_of_nonneg_right hsum (by positivity)
    _ ≤ _ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (normalized_tuple_high_rate_le hr w n M) hK

/-- The complete truncation-and-summation step. Its hypotheses are precisely
a weighted product bound and bounded-rate separated-grid convergence; the
actual microscopic probability estimate will discharge the latter. This is
an auxiliary reduction, not a claimed proof of Lemma 5.2 by assumption. -/
theorem ProfileLimit.tendsto_weighted_cyclic_array_sum {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {r : ℕ} (hr : 0 < r)
    (A : (n : ℕ) → (Fin r → Fin (n + 1)) → ℝ) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ᶠ n in atTop, ∀ i, |A n i| ≤ K * ∏ a, (w (n + 1)).rate (i a))
    (hsep : ∀ M : ℝ, 0 < M → ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i : Fin r → Fin (n + 1),
        (∀ a, (w (n + 1)).rate (i a) ≤ M) →
        (∀ a b : Fin r, a ≠ b →
          ζ ≤ |((i a).val + 1 : ℝ) / (n + 1 : ℕ) - ((i b).val + 1 : ℝ) / (n + 1 : ℕ)|) →
        |A n i| < ε) :
    Tendsto (fun n => (∑ i, A n i) / (n + 1 : ℕ) ^ r) atTop (𝓝 0) := by
  classical
  let T (M : ℝ) (n : ℕ) (i : Fin r → Fin (n + 1)) :=
    if ∀ a, (w (n + 1)).rate (i a) ≤ M then A n i else 0
  have htr (M : ℝ) (hM : 0 < M) :
      Tendsto (fun n => (∑ i, T M n i) / (n + 1 : ℕ) ^ r) atTop (𝓝 0) := by
    apply tendsto_cyclic_array_sum_of_separated hr (T M)
    · filter_upwards [hbound] with n hn i
      dsimp only [T]
      split_ifs with hi
      · calc
          |A n i| ≤ K * ∏ a, (w (n + 1)).rate (i a) := hn i
          _ ≤ K * M ^ r := by
            apply mul_le_mul_of_nonneg_left _ hK.le
            simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
              Finset.prod_le_prod (s := Finset.univ) (fun a _ => (w (n + 1)).positive (i a) |>.le)
                (fun a _ => hi a)
      · exact (abs_zero).trans_le (mul_nonneg hK.le (pow_nonneg hM.le _))
    · intro ζ hζ ε hε
      filter_upwards [hsep M hM ζ hζ ε hε] with n hn i hi
      dsimp only [T]
      split_ifs with hrate
      · exact hn i hrate hi
      · simpa only [abs_zero] using hε
  obtain ⟨C, hC, hmean⟩ := hf.eventually_rowMean_le
  let D : ℝ := K * r * C ^ (r - 1)
  have hD : 0 < D := mul_pos (mul_pos hK (Nat.cast_pos.mpr hr)) (pow_pos hC _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M, hM, htail⟩ := hf.highRateMass_small (show 0 < ε / 2 / D by positivity)
  have htail' := (tendsto_add_atTop_nat 1).eventually (htail M le_rfl)
  have htlim : Tendsto (fun n => |(∑ i, T M n i) / (n + 1 : ℕ) ^ r|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, abs_zero] using (htr M hM).norm
  have htr' := htlim.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity))
  filter_upwards [hbound, hmean, htail', htr'] with n hn hnmean hntail hntr
  rw [Real.dist_eq, sub_zero]
  have hhigh : 0 ≤ highRateMass w (n + 1) M := by
    unfold highRateMass
    exact div_nonneg (Finset.sum_nonneg (fun i _ => (w (n + 1)).positive i |>.le))
      (Nat.cast_nonneg _)
  have hmean0 : (0 : ℝ) ≤ (∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ) :=
    div_nonneg (Finset.sum_nonneg (fun i _ => (w (n + 1)).positive i |>.le)) (Nat.cast_nonneg _)
  have hp := pow_le_pow_left₀ hmean0 hnmean (r - 1)
  have he := cyclic_array_truncation_error hr w n M hK.le (A n) hn
  have he' : |(∑ i, A n i) / (n + 1 : ℕ) ^ r - (∑ i, T M n i) / (n + 1 : ℕ) ^ r| ≤
      D * highRateMass w (n + 1) M := by
    apply he.trans
    calc
      K * ((r : ℝ) * highRateMass w (n + 1) M *
          ((∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ)) ^ (r - 1)) =
          (K * r * highRateMass w (n + 1) M) *
            ((∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ)) ^ (r - 1) := by ring
      _ ≤ (K * r * highRateMass w (n + 1) M) * C ^ (r - 1) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg hK.le (Nat.cast_nonneg _)) hhigh)
      _ = D * highRateMass w (n + 1) M := by dsimp [D]; ring
  have hsmall : D * highRateMass w (n + 1) M < ε / 2 := by
    simpa only [mul_comm] using (lt_div_iff₀ hD).mp hntail
  have hntr' : |(∑ i, T M n i) / (n + 1 : ℕ) ^ r| < ε / 2 := hntr
  calc
    _ ≤ |(∑ i, A n i) / (n + 1 : ℕ) ^ r - (∑ i, T M n i) / (n + 1 : ℕ) ^ r| +
        |(∑ i, T M n i) / (n + 1 : ℕ) ^ r| := by
      simpa only [sub_add_cancel] using abs_add_le
        ((∑ i, A n i) / (n + 1 : ℕ) ^ r - (∑ i, T M n i) / (n + 1 : ℕ) ^ r)
        ((∑ i, T M n i) / (n + 1 : ℕ) ^ r)
    _ < ε := by linarith

def cyclicTupleProbability {n r : ℕ} (w : Weights n) (τ : Equiv.Perm (Fin r))
    (i : Fin r → Fin n) : ℝ :=
  (exponentialRace w).real {E | ∀ a, raceRank E (i a) = (i (τ a)).val + 1}

def cyclicScaledRaceTerm {n r : ℕ} (w : Weights n) (τ : Equiv.Perm (Fin r))
    (i : Fin r → Fin n) : ℝ := by
  classical
  exact if Function.Injective i then (n : ℝ) ^ r * cyclicTupleProbability w τ i else 0

/-- Exact signed error between the scaled rank probability and its finite
rate kernel, extended by zero outside the bulk. Repeated tuples contribute
zero probability, while their kernel contribution is explicitly retained. -/
def cyclicComparisonArray {n r : ℕ} (w : Weights n) (f : ℝ → ℝ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) (i : Fin r → Fin n) : ℝ := by
  classical
  exact if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
    g (fun a => ((i a).val + 1 : ℝ) / n) *
      (cyclicScaledRaceTerm w τ i - ∏ a, finiteCyclicDensity w f (i a) (i (τ a)))
  else 0

lemma sum_embedding_eq_sum_injective {n r : ℕ} (b : (Fin r → Fin n) → ℝ) :
    (∑ i : Fin r ↪ Fin n, b i) =
      ∑ i : Fin r → Fin n, if Function.Injective i then b i else 0 := by
  classical
  let e : (Fin r ↪ Fin n) ≃ {i : Fin r → Fin n // Function.Injective i} :=
    { toFun := fun i => ⟨i, i.injective⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑ i : {i : Fin r → Fin n // Function.Injective i}, b i.val := e.sum_comp _
    _ = _ := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype _ (by simp) b).symm

lemma cyclicRaceSum_eq_function_sum {n r : ℕ} (w : Weights n) (hn : 0 < n)
    (α : ℝ) (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicRaceSum w α τ g =
      ∑ i : Fin r → Fin n, if Function.Injective i then
        (if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
          g (fun a => ((i a).val + 1 : ℝ) / n) * cyclicTupleProbability w τ i else 0)
      else 0 := by
  classical
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simpa only [cyclicRaceSum, cyclicTupleProbability, div_le_iff₀ hN] using
    sum_embedding_eq_sum_injective (n := n) (r := r) (fun i =>
      if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
        g (fun a => ((i a).val + 1 : ℝ) / n) * cyclicTupleProbability w τ i else 0)

/-- Exact passage between the injective tuple sum in the paper and the full
cell-array error, including all repeated-index kernel terms. -/
lemma normalized_cyclicComparisonArray {n r : ℕ} (w : Weights n) (hn : 0 < n)
    (f : ℝ → ℝ) (α : ℝ) (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    (∑ i : Fin r → Fin n, cyclicComparisonArray w f α τ g i) / (n : ℝ) ^ r =
      cyclicRaceSum w α τ g - cyclicDeterministicSum w f α τ g := by
  classical
  have he (i : Fin r → Fin n) : cyclicComparisonArray w f α τ g i =
      (n : ℝ) ^ r *
        (if Function.Injective i then (if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
          g (fun a => ((i a).val + 1 : ℝ) / n) * cyclicTupleProbability w τ i else 0) else 0) -
        (if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
          g (fun a => ((i a).val + 1 : ℝ) / n) * ∏ a, finiteCyclicDensity w f (i a) (i (τ a))
        else 0) := by
    unfold cyclicComparisonArray cyclicScaledRaceTerm
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sub_div,
    mul_div_cancel_left₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hn.ne')),
    cyclicRaceSum_eq_function_sum w hn]
  rfl

lemma finiteCyclicDensity_bounds {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {n : ℕ} (i j : Fin n)
    (hj : ((j.val : ℝ) + 1) / n ≤ α) :
    0 ≤ finiteCyclicDensity (w n) f i j ∧
      finiteCyclicDensity (w n) f i j ≤ (w n).rate i /
        profileD profileMeasure f (profileQuantile profileMeasure f α) := by
  have hx : ((j.val : ℝ) + 1) / n ∈ Icc (0 : ℝ) α := ⟨by positivity, hj⟩
  have hq0 := profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hx.1, hx.2.trans_lt hα1⟩
  have hden := section3_denominator_lower hf hα0 hα1
  have hDx := hden.1.trans_le (hden.2 _ hx)
  refine ⟨div_nonneg (rateKernel_nonneg ((w n).positive i).le) hDx.le, ?_⟩
  exact (div_le_div_of_nonneg_right (rateKernel_le hq0 ((w n).positive i).le) hDx.le).trans
    (div_le_div_of_nonneg_left ((w n).positive i).le hden.1 (hden.2 _ hx))

/-- Both the actual probability and the finite kernel are dominated by the
same product of source rates. No rate truncation is used in this bound. -/
theorem ProfileLimit.cyclicComparisonArray_weighted_bound {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {r : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (τ : Equiv.Perm (Fin r)) {g : (Fin r → ℝ) → ℝ}
    (hg : ContinuousOn g (cyclicBulkCube r α)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ i : Fin r → Fin (n + 1),
      |cyclicComparisonArray (w (n + 1)) f α τ g i| ≤
        K * ∏ a, (w (n + 1)).rate (i a) := by
  classical
  obtain ⟨Kp, hKp, hprob⟩ := hf.weighted_bulk_cylinder r hα1
  have hcompact : IsCompact (cyclicBulkCube r α) := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hg
  let B := max C 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let d := profileD profileMeasure f (profileQuantile profileMeasure f α)
  have hd : 0 < d := (section3_denominator_lower hf hα0 hα1).1
  let Cd : ℝ := d⁻¹ ^ r
  have hCd : 0 ≤ Cd := pow_nonneg (inv_nonneg.mpr hd.le) _
  refine ⟨B * (Kp + Cd), mul_pos hB (add_pos_of_pos_of_nonneg hKp hCd), ?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hprob] with n hn i
  have hN : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hprod0 : 0 ≤ ∏ a, (w (n + 1)).rate (i a) :=
    Finset.prod_nonneg (fun a _ => (w (n + 1)).positive (i a) |>.le)
  unfold cyclicComparisonArray
  split_ifs with hi
  · have hx : (fun a => ((i a).val + 1 : ℝ) / (n + 1 : ℕ)) ∈ cyclicBulkCube r α :=
      fun a _ => ⟨by positivity, hi a⟩
    have hgB : |g (fun a => ((i a).val + 1 : ℝ) / (n + 1 : ℕ))| ≤ B :=
      (hC _ hx).trans (le_max_left _ _)
    have hR : 0 ≤ cyclicScaledRaceTerm (w (n + 1)) τ i ∧
        cyclicScaledRaceTerm (w (n + 1)) τ i ≤ Kp * ∏ a, (w (n + 1)).rate (i a) := by
      unfold cyclicScaledRaceTerm
      split_ifs with hinj
      · let ie : Fin r ↪ Fin (n + 1) := ⟨i, hinj⟩
        let je : Fin r ↪ Fin (n + 1) := ⟨fun a => i (τ a), hinj.comp τ.injective⟩
        have hj : ∀ a, ((je a).val : ℝ) + 1 ≤ α * (n + 1 : ℕ) :=
          fun a => (div_le_iff₀ hN).mp (hi (τ a))
        have hp := hn ie je hj
        refine ⟨mul_nonneg (pow_nonneg hN.le _) measureReal_nonneg, ?_⟩
        calc
          _ ≤ (n + 1 : ℕ) ^ r *
              (Kp / (n + 1 : ℕ) ^ r * ∏ a, (w (n + 1)).rate (i a)) :=
            mul_le_mul_of_nonneg_left hp (pow_nonneg hN.le _)
          _ = _ := by field_simp
      · exact ⟨le_rfl, mul_nonneg hKp.le hprod0⟩
    have hP : 0 ≤ ∏ a, finiteCyclicDensity (w (n + 1)) f (i a) (i (τ a)) :=
      Finset.prod_nonneg (fun a _ => (finiteCyclicDensity_bounds hf hα0 hα1 _ _ (hi (τ a))).1)
    have hPbound : (∏ a, finiteCyclicDensity (w (n + 1)) f (i a) (i (τ a))) ≤
        Cd * ∏ a, (w (n + 1)).rate (i a) := by
      calc
        _ ≤ ∏ a, (w (n + 1)).rate (i a) / d := Finset.prod_le_prod
          (fun a _ => (finiteCyclicDensity_bounds hf hα0 hα1 _ _ (hi (τ a))).1)
          (fun a _ => (finiteCyclicDensity_bounds hf hα0 hα1 _ _ (hi (τ a))).2)
        _ = _ := by
          simp only [Cd, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
          ring
    have hdiff : |cyclicScaledRaceTerm (w (n + 1)) τ i -
        ∏ a, finiteCyclicDensity (w (n + 1)) f (i a) (i (τ a))| ≤
        (Kp + Cd) * ∏ a, (w (n + 1)).rate (i a) := by
      have ht := abs_sub_le (cyclicScaledRaceTerm (w (n + 1)) τ i) 0
        (∏ a, finiteCyclicDensity (w (n + 1)) f (i a) (i (τ a)))
      simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hR.1, abs_of_nonneg hP] at ht
      nlinarith [hR.2]
    rw [abs_mul]
    calc
      _ ≤ B * ((Kp + Cd) * ∏ a, (w (n + 1)).rate (i a)) :=
        mul_le_mul hgB hdiff (abs_nonneg _) hB.le
      _ = _ := by ring
  · simpa only [abs_zero] using
      mul_nonneg (mul_nonneg hB.le (add_nonneg hKp.le hCd)) hprod0

/-- The complete finite-sum reduction of Lemma 5.2 to its bounded marked
asymptotic (1040–1045). The microscopic premise is explicit and must be
proved from the actual race; this declaration is not advertised as the
completed probabilistic lemma. Every other truncation, diagonal, profile,
integrability and signed-test-function step is discharged here. -/
theorem ProfileLimit.cyclic_local_of_bounded_marked_asymptotic
    {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f) {r : ℕ} (hr : 0 < r)
    {α : ℝ} (hα : α < 1) (τ : Equiv.Perm (Fin r))
    {g : (Fin r → ℝ) → ℝ} (hg : ContinuousOn g (cyclicBulkCube r α))
    (hmicro : ∀ M : ℝ, 0 < M → ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ i j : Fin r ↪ Fin n,
        (∀ a, (w n).rate (i a) ≤ M) →
        (∀ a, ((j a).val : ℝ) + 1 ≤ α * n) →
        (∀ a b : Fin r, a ≠ b → ζ * n ≤ |((j a).val : ℝ) - (j b).val|) →
        |(n : ℝ) ^ r * (exponentialRace (w n)).real
          {E | ∀ a, raceRank E (i a) = (j a).val + 1} -
          ∏ a, finiteCyclicDensity (w n) f (i a) (j a)| < ε) :
    Tendsto (fun n => cyclicRaceSum (w (n + 1)) α τ g) atTop
      (𝓝 (cyclicProfileIntegral f α τ g)) := by
  classical
  by_cases hα0 : 0 < α
  · obtain ⟨K, hK, hbound⟩ := hf.cyclicComparisonArray_weighted_bound hα0.le hα τ hg
    have hcompact : IsCompact (cyclicBulkCube r α) := isCompact_univ_pi (fun _ => isCompact_Icc)
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hg
    let B := max C 0
    have hB : 0 ≤ B := le_max_right _ _
    have hGB : ∀ x ∈ cyclicBulkCube r α, |g x| ≤ B :=
      fun x hx => (hC x hx).trans (le_max_left _ _)
    have hzero := hf.tendsto_weighted_cyclic_array_sum hr
      (fun n => cyclicComparisonArray (w (n + 1)) f α τ g) hK hbound
      (by
        intro M hM ζ hζ ε hε
        have heps : 0 < ε / (B + 1) := div_pos hε (by positivity)
        filter_upwards [(tendsto_add_atTop_nat 1).eventually (hmicro M hM ζ hζ _ heps)]
          with n hn i hrate hsep
        have hN : (0 : ℝ) < (n + 1 : ℕ) := by positivity
        unfold cyclicComparisonArray
        split_ifs with hbulk
        · have hinj : Function.Injective i := by
            intro a b he
            by_contra hab
            have hs := hsep a b hab
            rw [he, sub_self, abs_zero] at hs
            exact (not_le_of_gt hζ) hs
          let ie : Fin r ↪ Fin (n + 1) := ⟨i, hinj⟩
          let je : Fin r ↪ Fin (n + 1) := ⟨fun a => i (τ a), hinj.comp τ.injective⟩
          have hj : ∀ a, ((je a).val : ℝ) + 1 ≤ α * (n + 1 : ℕ) :=
            fun a => (div_le_iff₀ hN).mp (hbulk (τ a))
          have hs : ∀ a b : Fin r, a ≠ b →
              ζ * (n + 1 : ℕ) ≤ |((je a).val : ℝ) - (je b).val| := by
            intro a b hab
            have hh := hsep (τ a) (τ b) (fun he => hab (τ.injective he))
            rw [← sub_div, add_sub_add_right_eq_sub, abs_div, abs_of_pos hN] at hh
            exact (le_div_iff₀ hN).mp hh
          have hm := hn ie je hrate hj hs
          have hx : (fun a => ((i a).val + 1 : ℝ) / (n + 1 : ℕ)) ∈ cyclicBulkCube r α :=
            fun a _ => ⟨by positivity, hbulk a⟩
          rw [cyclicScaledRaceTerm, if_pos hinj, abs_mul]
          calc
            _ ≤ (B + 1) * |(n + 1 : ℕ) ^ r * cyclicTupleProbability (w (n + 1)) τ i -
                ∏ a, finiteCyclicDensity (w (n + 1)) f (i a) (i (τ a))| :=
              mul_le_mul_of_nonneg_right ((hGB _ hx).trans (le_add_of_nonneg_right zero_le_one))
                (abs_nonneg _)
            _ < (B + 1) * (ε / (B + 1)) :=
              mul_lt_mul_of_pos_left hm (by positivity)
            _ = ε := mul_div_cancel₀ _ (by positivity)
        · simpa only [abs_zero] using hε)
    have hd := hf.cyclic_deterministic_limit hα τ hg
    simp_rw [normalized_cyclicComparisonArray _ (Nat.succ_pos _)] at hzero
    simpa only [zero_add, sub_add_cancel] using hzero.add hd
  · have hαn : α ≤ 0 := le_of_not_gt hα0
    rw [cyclicProfileIntegral_of_nonpos f hαn hr τ g]
    simpa only [cyclicRaceSum_of_nonpos _ hαn hr τ g] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end Luce
