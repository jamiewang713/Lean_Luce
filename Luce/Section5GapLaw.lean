import Luce.Section3RaceDrawLaw
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Joint law of all normalized exponential race gaps

Source: `fixed_points.tex:1017–1024`, the exact memoryless gap representation.
The proof retains an arbitrary measurable function of the entire gap vector.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators

namespace Luce

lemma exponential_scale_to_unit {r : ℝ} (hr : 0 < r) :
    (expMeasure r).map (fun t => r * t) = expMeasure 1 := by
  let _ := isProbabilityMeasure_expMeasure hr
  let _ := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  apply Measure.ext_of_Iic
  intro t
  have hm : Measurable (fun x : ℝ => r * x) := measurable_const.mul measurable_id
  rw [Measure.map_apply hm measurableSet_Iic]
  have hpre : (fun x : ℝ => r * x) ⁻¹' Iic t = Iic (t / r) := by
    ext x
    simp only [mem_preimage, mem_Iic]
    exact le_div_iff₀' hr |>.symm
  rw [hpre, ← ofReal_cdf, ← ofReal_cdf, cdf_expMeasure_eq hr,
    cdf_expMeasure_eq (show (0 : ℝ) < 1 by norm_num)]
  have hs : 0 ≤ t / r ↔ 0 ≤ t := by
    rw [le_div_iff₀ hr, zero_mul]
  simp only [hs, one_mul]
  congr 2
  congr 1
  field_simp

/-- Identity-order gaps, constructed by exposing the first arrival and
subtracting it from the surviving clocks. A coordinate formula below
identifies this with the paper's remaining-rate times actual gap. -/
def identityNormalizedGaps : {n : ℕ} → Weights n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, _ => Fin.elim0
  | _n + 1, w, c => Fin.cons (w.total Finset.univ * c 0)
      (identityNormalizedGaps (w.removeFirst 0) (fun j => c j.succ - c 0))

theorem measurable_identityNormalizedGaps {n : ℕ} (w : Weights n) :
    Measurable (identityNormalizedGaps w) := by
  induction n with
  | zero => exact measurable_pi_iff.mpr (fun i => Fin.elim0 i)
  | succ n ih =>
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_const.mul (measurable_pi_apply 0)
    · exact (measurable_pi_apply j).comp ((ih (w.removeFirst 0)).comp
        (measurable_pi_iff.mpr (fun k =>
          (measurable_pi_apply k.succ).sub (measurable_pi_apply 0))))

lemma removeFirst_zero_total {n : ℕ} (w : Weights (n + 1)) :
    w.rate 0 + (w.removeFirst 0).total Finset.univ = w.total Finset.univ := by
  simp only [Weights.total, Weights.removeFirst, Equiv.swap_self, Equiv.refl_apply]
  exact (Fin.sum_univ_succ (fun j => w.rate j)).symm

lemma first_gap_density {n : ℕ} (w : Weights (n + 1)) (t : ℝ) :
    exponentialPDF (w.rate 0) t *
      ENNReal.ofReal (Real.exp (-((w.removeFirst 0).total Finset.univ * t))) =
    ENNReal.ofReal (w.rate 0 / w.total Finset.univ) *
      exponentialPDF (w.total Finset.univ) t := by
  have hW : 0 < w.total Finset.univ := w.total_pos Finset.univ_nonempty
  by_cases ht : 0 ≤ t
  · rw [exponentialPDF_of_nonneg ht, exponentialPDF_of_nonneg ht,
      ← ENNReal.ofReal_mul (mul_nonneg (w.positive 0).le (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (div_nonneg (w.positive 0).le hW.le)]
    congr 1
    rw [mul_assoc, ← Real.exp_add]
    have he : -(w.rate 0 * t) + -((w.removeFirst 0).total Finset.univ * t) =
        -(w.total Finset.univ * t) := by rw [← removeFirst_zero_total w]; ring
    rw [he]
    field_simp
  · simp only [exponentialPDF_of_neg (lt_of_not_ge ht), zero_mul, mul_zero]

/-- Memorylessness with an arbitrary measurable test of all residual
clocks, retaining the event specifying the rest of the elimination order. -/
theorem exponentialRace_surviving_order_integral {n : ℕ} (w : Weights n)
    {s : ℝ} (hs : 0 ≤ s) (H : (Fin n → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ c, if (∀ i, s < c i) ∧ StrictMono c then H (fun i => c i - s) else 0
      ∂exponentialRace w) =
    ENNReal.ofReal (Real.exp (-(w.total Finset.univ * s))) *
      ∫⁻ c, if StrictMono c then H c else 0 ∂exponentialRace w := by
  classical
  let F : (Fin n → ℝ) → ℝ≥0∞ := fun c => if StrictMono c then H c else 0
  have hF : Measurable F := Measurable.ite (measurableSet_strictMono_clocks n)
    hH measurable_const
  have hm : Measurable (fun c : Fin n → ℝ => fun i => c i - s) :=
    measurable_pi_iff.mpr (fun i => (measurable_pi_apply i).sub measurable_const)
  calc
    _ = ∫⁻ c in Set.univ.pi (fun _ : Fin n => Ioi s), F (fun i => c i - s)
        ∂exponentialRace w := by
      rw [← lintegral_indicator (MeasurableSet.univ_pi (fun _ => measurableSet_Ioi))]
      apply lintegral_congr
      intro c
      simp only [Set.indicator_apply, Set.mem_univ_pi, Set.mem_Ioi, F,
        strictMono_sub_const_iff]
      split_ifs <;> simp_all
    _ = ∫⁻ c, F c ∂(((exponentialRace w).restrict
        (Set.univ.pi (fun _ : Fin n => Ioi s))).map (fun c i => c i - s)) :=
      (lintegral_map hF hm).symm
    _ = _ := by
      rw [exponentialRace_residual_measure w hs, lintegral_smul_measure]
      rfl

/-- Standard independent exponentials, including the unique empty vector. -/
def standardGapLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => expMeasure 1)

instance standardGapLaw_isProbability (n : ℕ) : IsProbabilityMeasure (standardGapLaw n) := by
  let _ := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  unfold standardGapLaw
  infer_instance

lemma standardGapLaw_cons_integral (n : ℕ)
    (H : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x, H x ∂standardGapLaw (n + 1)) =
      ∫⁻ t, ∫⁻ u, H (Fin.cons t u) ∂standardGapLaw n ∂expMeasure 1 := by
  let _ := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => expMeasure 1) 0).symm e
  have hh := hp.lintegral_comp hH
  unfold standardGapLaw
  rw [← hh, lintegral_prod (fun a => H (e.symm a))
    (hH.comp e.symm.measurable).aemeasurable]
  congr 1
  funext t
  congr 1
  funext u
  congr 1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [e]

lemma measurable_finCons {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {a : Ω → ℝ} {b : Ω → Fin n → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => (Fin.cons (a x) (b x) : Fin (n + 1) → ℝ)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact Fin.cases ha (fun j => (measurable_pi_apply j).comp hb) i

/-- One step of the joint gap law. The first normalized gap has law Exp(1)
and factors from an arbitrary test of the full residual ordered gap vector. -/
theorem identityNormalizedGaps_order_recursion {n : ℕ} (w : Weights (n + 1))
    (H : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ c, if StrictMono c then H (identityNormalizedGaps w c) else 0
      ∂exponentialRace w) =
    ENNReal.ofReal (w.rate 0 / w.total Finset.univ) *
      ∫⁻ t, ∫⁻ u, if StrictMono u then
        H (Fin.cons t (identityNormalizedGaps (w.removeFirst 0) u)) else 0
        ∂exponentialRace (w.removeFirst 0) ∂expMeasure 1 := by
  classical
  let v := w.removeFirst 0
  let W := w.total Finset.univ
  let K : ℝ → ℝ≥0∞ := fun t => ∫⁻ u, if StrictMono u then
    H (Fin.cons t (identityNormalizedGaps v u)) else 0 ∂exponentialRace v
  have hgaps : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      (Fin.cons z.1 (identityNormalizedGaps v z.2) : Fin (n + 1) → ℝ)) :=
    measurable_finCons measurable_fst ((measurable_identityNormalizedGaps v).comp measurable_snd)
  have hK : Measurable K :=
    (Measurable.ite ((measurableSet_strictMono_clocks n).preimage measurable_snd)
      (hH.comp hgaps) measurable_const).lintegral_prod_right'
  let g : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun z =>
    if (∀ j, z.1 < z.2 j) ∧ StrictMono z.2 then
      H (Fin.cons (W * z.1) (identityNormalizedGaps v (fun j => z.2 j - z.1))) else 0
  have hg : Measurable g := by
    apply Measurable.ite ((measurableSet_first_before_background n).inter
      ((measurableSet_strictMono_clocks n).preimage measurable_snd)) _ measurable_const
    apply hH.comp
    apply measurable_finCons (measurable_const.mul measurable_fst)
    apply (measurable_identityNormalizedGaps v).comp
    exact measurable_pi_iff.mpr (fun j =>
      ((measurable_pi_apply j).comp measurable_snd).sub measurable_fst)
  have hdis : (∫⁻ c, if StrictMono c then H (identityNormalizedGaps w c) else 0
        ∂exponentialRace w) =
      ∫⁻ t, exponentialPDF (w.rate 0) t * ∫⁻ b, g (t, b) ∂exponentialRace v := by
    simpa only [g, v, W, identityNormalizedGaps, strictMono_clocks_iff,
      Fin.succAbove_zero, backgroundRace_zero] using
      exponentialRace_disintegrate w 0 g hg
  have hinner (t : ℝ) (ht : 0 ≤ t) :
      (∫⁻ b, g (t, b) ∂exponentialRace v) =
        ENNReal.ofReal (Real.exp (-(v.total Finset.univ * t))) * K (W * t) := by
    exact exponentialRace_surviving_order_integral v ht
      (fun b => H (Fin.cons (W * t) (identityNormalizedGaps v b)))
      (hH.comp (measurable_finCons measurable_const (measurable_identityNormalizedGaps v)))
  rw [hdis]
  calc
    _ = ∫⁻ t, ENNReal.ofReal (w.rate 0 / W) *
        (exponentialPDF W t * K (W * t)) := by
      apply lintegral_congr
      intro t
      by_cases ht : 0 ≤ t
      · rw [hinner t ht, ← mul_assoc, first_gap_density w]
        exact mul_assoc _ _ _
      · simp only [exponentialPDF_of_neg (lt_of_not_ge ht), zero_mul, mul_zero]
    _ = ENNReal.ofReal (w.rate 0 / W) *
        ∫⁻ t, exponentialPDF W t * K (W * t) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (w.rate 0 / W) * ∫⁻ t, K (W * t) ∂expMeasure W := by
      congr 1
      exact (lintegral_withDensity_eq_lintegral_mul _
        ((measurable_exponentialPDFReal W).ennreal_ofReal)
        (hK.comp (measurable_const.mul measurable_id))).symm
    _ = _ := by
      congr 1
      have hm : Measurable (fun t : ℝ => W * t) := measurable_const.mul measurable_id
      rw [← lintegral_map hK hm, exponential_scale_to_unit
        (w.total_pos Finset.univ_nonempty)]

/-- The entire normalized gap vector factors from the identity elimination
order. The test function is arbitrary and need not factor over coordinates. -/
theorem exponentialRace_identityNormalizedGaps_integral {n : ℕ} (w : Weights n)
    (H : (Fin n → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ c, if StrictMono c then H (identityNormalizedGaps w c) else 0
      ∂exponentialRace w) =
    ENNReal.ofReal (w.mass (Equiv.refl (Fin n))) * ∫⁻ u, H u ∂standardGapLaw n := by
  classical
  induction n with
  | zero =>
    have hc : (fun u : Fin 0 → ℝ => H u) = fun _ => H Fin.elim0 := by
      funext u
      congr 1
      exact Subsingleton.elim _ _
    simp only [identityNormalizedGaps, StrictMono, IsEmpty.forall_iff, if_true,
      Weights.mass, Fintype.prod_empty, ENNReal.ofReal_one, one_mul,
      lintegral_const, measure_univ, mul_one]
    rw [hc]
    simp
  | succ n ih =>
    rw [identityNormalizedGaps_order_recursion w H hH]
    have hh (t : ℝ) := ih (w.removeFirst 0) (fun u => H (Fin.cons t u))
      (hH.comp (measurable_finCons measurable_const measurable_id))
    simp_rw [hh]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
    have hm := exponentialRace_order_recursion w
    rw [exponentialRace_identity_order_probability,
      exponentialRace_identity_order_probability] at hm
    rw [← hm, ← standardGapLaw_cons_integral n H hH]

/-- Equality of finite measures, equivalent to every joint normalized gap
event having the independent Exp(1) probability times the order probability. -/
theorem exponentialRace_identityNormalizedGaps {n : ℕ} (w : Weights n) :
    ((exponentialRace w).restrict {c | StrictMono c}).map (identityNormalizedGaps w) =
      ENNReal.ofReal (w.mass (Equiv.refl (Fin n))) • standardGapLaw n := by
  classical
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_identityNormalizedGaps w) hA,
    Measure.restrict_apply (hA.preimage (measurable_identityNormalizedGaps w)),
    Measure.smul_apply, smul_eq_mul]
  have hh := exponentialRace_identityNormalizedGaps_integral w
    (A.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hA)
  rw [lintegral_indicator_fun_one hA] at hh
  have he : (fun c => if StrictMono c then A.indicator (fun _ => (1 : ℝ≥0∞))
      (identityNormalizedGaps w c) else 0) =
      ((identityNormalizedGaps w) ⁻¹' A ∩ {c | StrictMono c}).indicator (fun _ => 1) := by
    funext c
    simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [he, lintegral_indicator_fun_one
    ((hA.preimage (measurable_identityNormalizedGaps w)).inter (measurableSet_strictMono_clocks n))] at hh
  exact hh

/-- Rates listed in a specified elimination order; no equality between
different label rates is imposed. -/
def orderedWeights {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n)) : Weights n where
  rate q := w.rate (σ q)
  positive q := w.positive (σ q)

/-- The normalized gap vector on a specified elimination order. -/
def orderedNormalizedGaps {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n))
    (c : Fin n → ℝ) : Fin n → ℝ :=
  identityNormalizedGaps (orderedWeights w σ) (fun q => c (σ q))

theorem measurable_orderedNormalizedGaps {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) : Measurable (orderedNormalizedGaps w σ) :=
  (measurable_identityNormalizedGaps (orderedWeights w σ)).comp
    (measurable_pi_iff.mpr (fun q => measurable_pi_apply (σ q)))

theorem exponentialRace_orderedNormalizedGaps_integral {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (H : (Fin n → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ c, if StrictMono (fun q => c (σ q)) then H (orderedNormalizedGaps w σ c) else 0
      ∂exponentialRace w) =
    ENNReal.ofReal (w.mass σ) * ∫⁻ u, H u ∂standardGapLaw n := by
  classical
  let v := orderedWeights w σ
  let _ : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ
  have hp : MeasurePreserving e (exponentialRace v) (exponentialRace w) :=
    measurePreserving_piCongrLeft (fun i => expMeasure (w.rate i)) σ
  have hF : Measurable (fun c => if StrictMono c then H (identityNormalizedGaps v c) else 0) :=
    Measurable.ite (measurableSet_strictMono_clocks n)
      (hH.comp (measurable_identityNormalizedGaps v)) measurable_const
  have hh := (MeasurePreserving.symm e hp).lintegral_comp hF
  change (∫⁻ c, if StrictMono (fun q => c (σ q)) then H (orderedNormalizedGaps w σ c) else 0
      ∂exponentialRace w) =
    ∫⁻ c, if StrictMono c then H (identityNormalizedGaps v c) else 0 ∂exponentialRace v at hh
  rw [hh, exponentialRace_identityNormalizedGaps_integral v H hH]
  rfl

/-- Source equation `eq:race-gap-representation`, as the full joint measure
identity on every elimination order. In particular, normalized gaps remain
mutually independent after the complete order has been specified. -/
theorem exponentialRace_orderedNormalizedGaps {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) :
    ((exponentialRace w).restrict {c | StrictMono (fun q => c (σ q))}).map
        (orderedNormalizedGaps w σ) =
      ENNReal.ofReal (w.mass σ) • standardGapLaw n := by
  classical
  have hs : MeasurableSet {c : Fin n → ℝ | StrictMono (fun q => c (σ q))} :=
    (measurableSet_strictMono_clocks n).preimage
      (measurable_pi_iff.mpr (fun q => measurable_pi_apply (σ q)))
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_orderedNormalizedGaps w σ) hA,
    Measure.restrict_apply (hA.preimage (measurable_orderedNormalizedGaps w σ)),
    Measure.smul_apply, smul_eq_mul]
  have hh := exponentialRace_orderedNormalizedGaps_integral w σ
    (A.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hA)
  rw [lintegral_indicator_fun_one hA] at hh
  have he : (fun c => if StrictMono (fun q => c (σ q)) then
      A.indicator (fun _ => (1 : ℝ≥0∞)) (orderedNormalizedGaps w σ c) else 0) =
      ((orderedNormalizedGaps w σ) ⁻¹' A ∩ {c | StrictMono (fun q => c (σ q))}).indicator
        (fun _ => 1) := by
    funext c
    simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [he, lintegral_indicator_fun_one
    ((hA.preimage (measurable_orderedNormalizedGaps w σ)).inter hs)] at hh
  exact hh

/-- The gap vector obtained from the actual sorted draw permutation. -/
def raceNormalizedGaps {n : ℕ} (w : Weights n) (c : Fin n → ℝ) : Fin n → ℝ :=
  orderedNormalizedGaps w (raceDraw c) c

theorem measurable_raceNormalizedGaps {n : ℕ} (w : Weights n) :
    Measurable (raceNormalizedGaps w) := by
  let _ : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hm : Measurable (fun z : (Equiv.Perm (Fin n)) × (Fin n → ℝ) =>
      orderedNormalizedGaps w z.1 z.2) :=
    measurable_from_prod_countable_right (fun σ => measurable_orderedNormalizedGaps w σ)
  exact hm.comp ((measurable_raceDraw n).prodMk measurable_id)

theorem exponentialRace_raceNormalizedGaps_restrict_order {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) :
    ((exponentialRace w).restrict {c | raceDraw c = σ}).map (raceNormalizedGaps w) =
      ENNReal.ofReal (w.mass σ) • standardGapLaw n := by
  classical
  have he : {c : Fin n → ℝ | raceDraw c = σ} =ᵐ[exponentialRace w]
      {c | StrictMono (fun q => c (σ q))} := by
    filter_upwards [exponentialRace_injective_ae w] with c hc
    apply propext
    change raceDraw c = σ ↔ StrictMono (fun q => c (σ q))
    rw [raceDraw_eq c hc]
    exact drawPermutation_eq_iff_strictMono c hc σ
  have hs : MeasurableSet {c : Fin n → ℝ | raceDraw c = σ} := by
    have hh : MeasurableSet ((raceDraw : (Fin n → ℝ) → Equiv.Perm (Fin n)) ⁻¹' {σ}) :=
      (measurable_raceDraw n) (by trivial)
    exact hh
  calc
    _ = ((exponentialRace w).restrict {c | raceDraw c = σ}).map
        (orderedNormalizedGaps w σ) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hs] with c hc
      simp only [raceNormalizedGaps, hc]
    _ = _ := by
      rw [Measure.restrict_congr_set he]
      exact exponentialRace_orderedNormalizedGaps w σ

/-- Remaining rate just before the clock at position q rings. Position q
is zero-based, so this is the paper's W_q and includes the q-th clock. -/
def orderedRemainingRate {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n))
    (q : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (q ≤ ·), w.rate (σ k)

/-- The clock immediately preceding position q, with the sentinel T₀=0. -/
def previousOrderedTime {n : ℕ} (c : Fin n → ℝ) (q : Fin n) : ℝ :=
  if h : q.val = 0 then 0 else c ⟨q.val - 1, by omega⟩

/-- A gap between successive ordered clocks, including the initial gap. -/
def identityGapDuration {n : ℕ} (c : Fin n → ℝ) (q : Fin n) : ℝ :=
  c q - previousOrderedTime c q

lemma orderedRemainingRate_identity_zero {n : ℕ} (w : Weights (n + 1)) :
    orderedRemainingRate w (Equiv.refl _) 0 = w.total Finset.univ := by
  simp [orderedRemainingRate, Weights.total]

lemma orderedRemainingRate_identity_succ {n : ℕ} (w : Weights (n + 1)) (q : Fin n) :
    orderedRemainingRate w (Equiv.refl _) q.succ =
      orderedRemainingRate (w.removeFirst 0) (Equiv.refl _) q := by
  simp only [orderedRemainingRate, Finset.sum_filter, Equiv.refl_apply]
  rw [Fin.sum_univ_succ]
  simp [Weights.removeFirst]

lemma identityGapDuration_succ {n : ℕ} (c : Fin (n + 1) → ℝ) (q : Fin n) :
    identityGapDuration c q.succ =
      identityGapDuration (fun j => c j.succ - c 0) q := by
  unfold identityGapDuration previousOrderedTime
  simp only [Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
    Nat.add_sub_cancel]
  split_ifs with hq
  · have hzero : q.castSucc = (0 : Fin (n + 1)) := Fin.ext hq
    change c q.succ - c q.castSucc = c q.succ - c 0 - 0
    rw [hzero, sub_zero]
  · have he : (⟨q.val - 1, by omega⟩ : Fin n).succ = q.castSucc := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    change c q.succ - c q.castSucc =
      (c q.succ - c 0) - (c ((⟨q.val - 1, by omega⟩ : Fin n).succ) - c 0)
    rw [he]
    ring

/-- The recursive random vector is exactly the remaining rate multiplied
by the actual consecutive-clock gap, not a separately assumed noise vector. -/
theorem identityNormalizedGaps_eq_rate_mul_gap {n : ℕ} (w : Weights n)
    (c : Fin n → ℝ) (q : Fin n) :
    identityNormalizedGaps w c q =
      orderedRemainingRate w (Equiv.refl _) q * identityGapDuration c q := by
  induction n with
  | zero => exact Fin.elim0 q
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) q
    · simp [identityNormalizedGaps, orderedRemainingRate_identity_zero,
        identityGapDuration, previousOrderedTime]
    · simp only [identityNormalizedGaps, Fin.cons_succ]
      rw [ih, orderedRemainingRate_identity_succ, identityGapDuration_succ]

/-- Literal coordinate form of the paper's ξ_q = W_q(T_(q+1)−T_q), for
every specified elimination order, including q=0. -/
theorem orderedNormalizedGaps_eq_rate_mul_gap {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ℝ) (q : Fin n) :
    orderedNormalizedGaps w σ c q = orderedRemainingRate w σ q *
      (c (σ q) - previousOrderedTime (fun k => c (σ k)) q) := by
  exact identityNormalizedGaps_eq_rate_mul_gap (orderedWeights w σ) (fun k => c (σ k)) q

theorem orderedRemainingRate_pos {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) : 0 < orderedRemainingRate w σ q := by
  apply Finset.sum_pos (fun k _ => w.positive (σ k))
  exact ⟨q, by simp⟩

/-- The literal gap representation has a strictly positive denominator. -/
theorem ordered_gap_eq_normalized_div_rate {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ℝ) (q : Fin n) :
    c (σ q) - previousOrderedTime (fun k => c (σ k)) q =
      orderedNormalizedGaps w σ c q / orderedRemainingRate w σ q := by
  rw [orderedNormalizedGaps_eq_rate_mul_gap]
  field_simp [ne_of_gt (orderedRemainingRate_pos w σ q)]

/-- On the actual ordered positive clocks, the suffix rate is exactly the
total rate surviving strictly after the preceding arrival. -/
theorem orderedRemainingRate_eq_surviving_sum {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ℝ)
    (horder : StrictMono (fun k => c (σ k))) (hpos : ∀ i, 0 < c i) (q : Fin n) :
    orderedRemainingRate w σ q =
      ∑ i, if previousOrderedTime (fun k => c (σ k)) q < c i then w.rate i else 0 := by
  classical
  rw [← Equiv.sum_comp σ]
  simp only [orderedRemainingRate, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  have he : previousOrderedTime (fun k => c (σ k)) q < c (σ k) ↔ q ≤ k := by
    unfold previousOrderedTime
    split_ifs with hq
    · have hle : q ≤ k := by change q.val ≤ k.val; omega
      exact iff_of_true (hpos _) hle
    · rw [horder.lt_iff_lt]
      change q.val - 1 < k.val ↔ q.val ≤ k.val
      omega
  simp only [he]

/-- Summing all elimination orders removes the conditioning without
changing the product law of normalized gaps. -/
theorem exponentialRace_raceNormalizedGaps_integral {n : ℕ} (w : Weights n)
    (H : (Fin n → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ c, H (raceNormalizedGaps w c) ∂exponentialRace w) =
      ∫⁻ u, H u ∂standardGapLaw n := by
  classical
  have hs (σ : Equiv.Perm (Fin n)) : MeasurableSet {c : Fin n → ℝ | raceDraw c = σ} := by
    have hh : MeasurableSet ((raceDraw : (Fin n → ℝ) → Equiv.Perm (Fin n)) ⁻¹' {σ}) :=
      (measurable_raceDraw n) (by trivial)
    exact hh
  have hpart (c : Fin n → ℝ) : H (raceNormalizedGaps w c) =
      ∑ σ : Equiv.Perm (Fin n), if raceDraw c = σ then H (raceNormalizedGaps w c) else 0 := by
    simp
  have hpiece (σ : Equiv.Perm (Fin n)) :
      (∫⁻ c, if raceDraw c = σ then H (raceNormalizedGaps w c) else 0 ∂exponentialRace w) =
        ENNReal.ofReal (w.mass σ) * ∫⁻ u, H u ∂standardGapLaw n := by
    calc
      _ = ∫⁻ c in {c | raceDraw c = σ}, H (raceNormalizedGaps w c) ∂exponentialRace w := by
        rw [← lintegral_indicator (hs σ)]
        apply lintegral_congr
        intro c
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
      _ = ∫⁻ u, H u ∂(((exponentialRace w).restrict {c | raceDraw c = σ}).map
          (raceNormalizedGaps w)) := (lintegral_map hH (measurable_raceNormalizedGaps w)).symm
      _ = _ := by
        rw [exponentialRace_raceNormalizedGaps_restrict_order, lintegral_smul_measure]
        rfl
  calc
    _ = ∫⁻ c, ∑ σ : Equiv.Perm (Fin n),
        if raceDraw c = σ then H (raceNormalizedGaps w c) else 0 ∂exponentialRace w :=
      lintegral_congr hpart
    _ = ∑ σ : Equiv.Perm (Fin n), ENNReal.ofReal (w.mass σ) *
        ∫⁻ u, H u ∂standardGapLaw n := by
      rw [lintegral_finsetSum]
      · simp_rw [hpiece]
      · intro σ _
        exact Measurable.ite (hs σ) (hH.comp (measurable_raceNormalizedGaps w)) measurable_const
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun σ _ => (w.mass_pos σ).le),
        Weights.sum_mass]
      simp

theorem exponentialRace_raceNormalizedGaps {n : ℕ} (w : Weights n) :
    (exponentialRace w).map (raceNormalizedGaps w) = standardGapLaw n := by
  classical
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_raceNormalizedGaps w) hA]
  have hh := exponentialRace_raceNormalizedGaps_integral w
    (A.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hA)
  rw [lintegral_indicator_fun_one hA] at hh
  have he : (fun c => A.indicator (fun _ => (1 : ℝ≥0∞)) (raceNormalizedGaps w c)) =
      ((raceNormalizedGaps w) ⁻¹' A).indicator (fun _ => 1) := by
    funext c
    rfl
  rw [he, lintegral_indicator_fun_one (hA.preimage (measurable_raceNormalizedGaps w))] at hh
  exact hh

theorem measurePreserving_raceNormalizedGaps {n : ℕ} (w : Weights n) :
    MeasurePreserving (raceNormalizedGaps w) (exponentialRace w) (standardGapLaw n) :=
  ⟨measurable_raceNormalizedGaps w, exponentialRace_raceNormalizedGaps w⟩

/-- Any deterministic collection of distinct normalized gap coordinates
has the corresponding product exponential law. -/
theorem standardGapLaw_select {n r : ℕ} (q : Fin r ↪ Fin n) :
    MeasurePreserving (fun u : Fin n → ℝ => fun a => u (q a))
      (standardGapLaw n) (standardGapLaw r) := by
  let _ := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  refine ⟨measurable_pi_iff.mpr (fun a => measurable_pi_apply (q a)), ?_⟩
  have hi := (iIndepFun_pi (μ := fun _ : Fin n => expMeasure 1)
    (X := fun _ => id) (fun _ => aemeasurable_id)).precomp q.injective
  have he := hi.map_fun_eq_pi_map (fun a => (measurable_pi_apply (q a)).aemeasurable)
  change (standardGapLaw n).map (fun u a => u (q a)) =
    Measure.pi (fun a => (standardGapLaw n).map (fun u => u (q a))) at he
  rw [he]
  congr 1
  funext a
  exact (measurePreserving_eval (fun _ : Fin n => expMeasure 1) (q a)).map_eq

theorem measurePreserving_selectedNormalizedGaps {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) :
    MeasurePreserving (fun c => fun a => raceNormalizedGaps w c (q a))
      (exponentialRace w) (standardGapLaw r) :=
  (standardGapLaw_select q).comp (measurePreserving_raceNormalizedGaps w)

end Luce
