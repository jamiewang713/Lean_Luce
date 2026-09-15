import Luce.Section3ProfileKernels
import Luce.Section4ExponentialFacts

/-!
# The exponential-gap Taylor estimate in Lemma 5.2

Source: `fixed_points.tex:1035–1048`. The gap probability below is the
actual exponential measure of the finite gap. Its error estimate is global
in the gap length; there is no unproved small-gap event or bounded clock.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Luce

set_option backward.isDefEq.respectTransparency false

/-- Probability mass of a finite gap starting at `s` with length `h`.
The equality with the actual exponential measure is proved below. -/
def exponentialGapMass (a s h : ℝ) : ℝ :=
  survivalKernel s a - survivalKernel (s + h) a

lemma exponentialGapMass_nonneg {a s h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) :
    0 ≤ exponentialGapMass a s h :=
  sub_nonneg.mpr (survivalKernel_antitone_time ha (by linarith))

lemma exponentialGapMass_le {a s h : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    exponentialGapMass a s h ≤ a * h := by
  have he := abs_survivalKernel_sub_le ha hs (add_nonneg hs hh)
  have heq (t : ℝ) : survivalKernel a t = survivalKernel t a := by
    unfold survivalKernel
    congr 1
    ring
  simp only [heq] at he
  change |exponentialGapMass a s h| ≤ _ at he
  rw [abs_of_nonneg (exponentialGapMass_nonneg ha hh)] at he
  simpa only [show s - (s + h) = -h by ring, abs_neg, abs_of_nonneg hh] using he

lemma exponentialGapMass_eq_measure {a s h : ℝ}
    (ha : 0 < a) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    (expMeasure a).real (Ioo s (s + h)) = exponentialGapMass a s h := by
  letI := isProbabilityMeasure_expMeasure ha
  by_cases hh0 : h = 0
  · simp [hh0, exponentialGapMass]
  have hhpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
  have he : Ioi s \ Ici (s + h) = Ioo s (s + h) := by
    ext x
    simp only [mem_diff, mem_Ioi, mem_Ici, not_le, mem_Ioo]
  rw [← he, measureReal_sdiff (by
    intro x hx
    have hx' : s + h ≤ x := hx
    show s < x
    linarith)
    measurableSet_Ici (measure_ne_top _ _)]
  rw [measureReal_def, measureReal_def, expMeasure_Ioi ha hs,
    expMeasure_Ici ha (add_nonneg hs hh), ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  unfold exponentialGapMass survivalKernel
  congr 2 <;> ring

/-- A first-order expansion with a global quadratic bound, including `h=0`.
The harmless constant one (rather than one half) suffices for the source's
uniform mixed-moment argument. -/
theorem exponentialGapMass_taylor {a s h : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    |exponentialGapMass a s h - rateKernel s a * h| ≤ a ^ 2 * h ^ 2 := by
  let R : ℝ → ℝ := fun u => survivalKernel s a - survivalKernel (s + u) a -
    rateKernel s a * u
  have hd (u : ℝ) : HasDerivAt R (a * (survivalKernel (s + u) a - survivalKernel s a)) u := by
    have hexp : HasDerivAt (fun u : ℝ => survivalKernel (s + u) a)
        (-a * survivalKernel (s + u) a) u := by
      convert! (((hasDerivAt_id u).const_add s).const_mul (-a)).exp using 1
      · funext v
        dsimp only [survivalKernel, id_eq]
        congr 1
        ring
      · dsimp only [survivalKernel, id_eq]
        ring_nf
    convert! ((hasDerivAt_const u (survivalKernel s a)).sub hexp).sub
      ((hasDerivAt_id u).const_mul (rateKernel s a)) using 1
    change a * (survivalKernel (s + u) a - survivalKernel s a) =
      0 - -a * survivalKernel (s + u) a - a * survivalKernel s a * 1
    ring
  have hb (u : ℝ) (hu : u ∈ Icc (0 : ℝ) h) :
      ‖a * (survivalKernel (s + u) a - survivalKernel s a)‖ ≤ a ^ 2 * h := by
    have he := abs_survivalKernel_sub_le ha (add_nonneg hs hu.1) hs
    have heq (t : ℝ) : survivalKernel a t = survivalKernel t a := by
      unfold survivalKernel
      congr 1
      ring
    simp only [heq, show s + u - s = u by ring, abs_of_nonneg hu.1] at he
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha]
    calc
      _ ≤ a * (a * u) := mul_le_mul_of_nonneg_left he ha
      _ ≤ a * (a * h) := by gcongr; exact hu.2
      _ = _ := by ring
  have he := (convex_Icc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd u).hasDerivWithinAt) hb (show (0 : ℝ) ∈ Icc 0 h from ⟨le_rfl, hh⟩)
    (show h ∈ Icc 0 h from ⟨hh, le_rfl⟩)
  simpa [R, exponentialGapMass, Real.norm_eq_abs, abs_of_nonneg hh, pow_two, mul_assoc] using he

/-- Telescoping with coordinate-dependent envelopes. In particular, zero
envelopes are allowed: no division by a gap or a rate is performed. -/
theorem abs_prod_sub_prod_le_relative {ι : Type*} (S : Finset ι)
    (u v z e : ι → ℝ)
    (hu : ∀ i ∈ S, |u i| ≤ z i) (hv : ∀ i ∈ S, |v i| ≤ z i)
    (hz : ∀ i ∈ S, 0 ≤ z i) (he : ∀ i ∈ S, 0 ≤ e i)
    (herr : ∀ i ∈ S, |u i - v i| ≤ e i * z i) :
    |(∏ i ∈ S, u i) - ∏ i ∈ S, v i| ≤ (∑ i ∈ S, e i) * ∏ i ∈ S, z i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert b S hb ih =>
    have hu' : ∀ i ∈ S, |u i| ≤ z i := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hv' : ∀ i ∈ S, |v i| ≤ z i := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hz' : ∀ i ∈ S, 0 ≤ z i := fun i hi => hz i (Finset.mem_insert_of_mem hi)
    have he' : ∀ i ∈ S, 0 ≤ e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have herr' : ∀ i ∈ S, |u i - v i| ≤ e i * z i :=
      fun i hi => herr i (Finset.mem_insert_of_mem hi)
    have hp : |∏ i ∈ S, u i| ≤ ∏ i ∈ S, z i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) hu'
    have hp0 := Finset.prod_nonneg hz'
    have hs0 := Finset.sum_nonneg he'
    have huvb := herr b (Finset.mem_insert_self _ _)
    have hvb := hv b (Finset.mem_insert_self _ _)
    have hzb := hz b (Finset.mem_insert_self _ _)
    have heb := he b (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hb, Finset.prod_insert hb, Finset.prod_insert hb,
      Finset.sum_insert hb]
    calc
      _ = |(u b - v b) * (∏ i ∈ S, u i) +
          v b * ((∏ i ∈ S, u i) - ∏ i ∈ S, v i)| := by congr 1; ring
      _ ≤ |u b - v b| * |∏ i ∈ S, u i| +
          |v b| * |(∏ i ∈ S, u i) - ∏ i ∈ S, v i| := by
        simpa only [abs_mul] using abs_add_le
          ((u b - v b) * (∏ i ∈ S, u i))
          (v b * ((∏ i ∈ S, u i) - ∏ i ∈ S, v i))
      _ ≤ (e b * z b) * (∏ i ∈ S, z i) +
          z b * ((∑ i ∈ S, e i) * ∏ i ∈ S, z i) := by
        exact add_le_add (mul_le_mul huvb hp (abs_nonneg _) (mul_nonneg heb hzb))
          (mul_le_mul hvb (ih hu' hv' hz' he' herr') (abs_nonneg _) hzb)
      _ = _ := by ring

/-- The precise multigap error used in the source's mixed-moment step.
It retains all gap factors and remains true when any gap has length zero. -/
theorem prod_exponentialGapMass_taylor {ι : Type*} [Fintype ι]
    (a s h : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 ≤ s i) (hh : ∀ i, 0 ≤ h i) :
    |(∏ i, exponentialGapMass (a i) (s i) (h i)) -
      ∏ i, rateKernel (s i) (a i) * h i| ≤
      (∑ i, a i * h i) * ∏ i, a i * h i := by
  apply abs_prod_sub_prod_le_relative
  · intro i _
    rw [abs_of_nonneg (exponentialGapMass_nonneg (ha i) (hh i))]
    exact exponentialGapMass_le (ha i) (hs i) (hh i)
  · intro i _
    rw [abs_of_nonneg (mul_nonneg (rateKernel_nonneg (ha i)) (hh i))]
    exact mul_le_mul_of_nonneg_right (rateKernel_le (hs i) (ha i)) (hh i)
  · intro i _; exact mul_nonneg (ha i) (hh i)
  · intro i _; exact mul_nonneg (ha i) (hh i)
  · intro i _
    convert exponentialGapMass_taylor (ha i) (hs i) (hh i) using 1 <;> ring

/-- Uniform time variation of the marked density for a bounded marked rate.
This bound needs neither a positive lower bound on the rate nor bounded time. -/
theorem gap_abs_rateKernel_time_sub_le {a s t : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |rateKernel s a - rateKernel t a| ≤ a ^ 2 * |s - t| := by
  have he := abs_survivalKernel_sub_le ha hs ht
  have heq (v : ℝ) : survivalKernel a v = survivalKernel v a := by
    unfold survivalKernel
    congr 1
    ring
  simp only [heq] at he
  rw [rateKernel, rateKernel, ← mul_sub, abs_mul, abs_of_nonneg ha]
  calc
    _ ≤ a * (a * |s - t|) := mul_le_mul_of_nonneg_left he ha
    _ = _ := by ring

/-- The reciprocal denominator error is controlled by the actual common
positive reservoir lower bound. No upper bound on the remaining rate is used. -/
theorem abs_gap_coefficient_sub_le {a s t W D b : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hb : 0 < b) (hW : b ≤ W) (hD : b ≤ D) :
    |rateKernel s a / W - rateKernel t a / D| ≤
      a ^ 2 / b * |s - t| + a / b ^ 2 * |W - D| := by
  have hWpos := hb.trans_le hW
  have hDpos := hb.trans_le hD
  have hden : b ^ 2 ≤ W * D := by nlinarith
  have heq : rateKernel s a / W - rateKernel t a / D =
      (rateKernel s a - rateKernel t a) / W +
        rateKernel t a * (D - W) / (W * D) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(rateKernel s a - rateKernel t a) / W| +
        |rateKernel t a * (D - W) / (W * D)| := abs_add_le _ _
    _ = |rateKernel s a - rateKernel t a| / W +
        rateKernel t a * |W - D| / (W * D) := by
      rw [abs_div, abs_of_pos hWpos, abs_div, abs_mul,
        abs_of_nonneg (rateKernel_nonneg ha), abs_sub_comm D W,
        abs_of_pos (mul_pos hWpos hDpos)]
    _ ≤ (a ^ 2 * |s - t|) / b + a * |W - D| / b ^ 2 := by
      apply add_le_add
      · exact div_le_div₀ (mul_nonneg (sq_nonneg a) (abs_nonneg _))
          (gap_abs_rateKernel_time_sub_le ha hs ht) hb hW
      · exact div_le_div₀ (mul_nonneg ha (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (rateKernel_le ht ha) (abs_nonneg _))
          (sq_pos_of_pos hb) hden
    _ = _ := by ring

/-- Explicit rescaled Taylor bound under the finite reservoir inequality.
Only this auxiliary estimate assumes a bound `M` on marked rates. -/
theorem rescaled_prod_exponentialGapMass_taylor {r : ℕ}
    (a s W ξ : Fin r → ℝ) {N b M : ℝ}
    (hN : 0 < N) (hb : 0 < b) (hM : 0 ≤ M)
    (ha : ∀ i, 0 ≤ a i) (haM : ∀ i, a i ≤ M)
    (hs : ∀ i, 0 ≤ s i) (hW : ∀ i, b * N ≤ W i) (hξ : ∀ i, 0 ≤ ξ i) :
    |N ^ r * (∏ i, exponentialGapMass (a i) (s i) (ξ i / W i)) -
      (∏ i, rateKernel (s i) (a i) / (W i / N)) * (∏ i, ξ i)| ≤
      (M / (b * N)) ^ (r + 1) * N ^ r * ((∑ i, ξ i) * ∏ i, ξ i) := by
  have hWp (i : Fin r) : 0 < W i := (mul_pos hb hN).trans_le (hW i)
  have hh (i : Fin r) : 0 ≤ ξ i / W i := div_nonneg (hξ i) (hWp i).le
  have hcoeff (i : Fin r) : a i * (ξ i / W i) ≤ M / (b * N) * ξ i := by
    calc
      _ = (a i * ξ i) / W i := by ring
      _ ≤ (M * ξ i) / (b * N) := div_le_div₀ (mul_nonneg hM (hξ i))
        (mul_le_mul_of_nonneg_right (haM i) (hξ i)) (mul_pos hb hN) (hW i)
      _ = _ := by ring
  have hc : 0 ≤ M / (b * N) := div_nonneg hM (mul_pos hb hN).le
  have hsp : (∑ i, a i * (ξ i / W i)) * (∏ i, a i * (ξ i / W i)) ≤
      (M / (b * N)) ^ (r + 1) * ((∑ i, ξ i) * ∏ i, ξ i) := by
    calc
      _ ≤ (∑ i, M / (b * N) * ξ i) * (∏ i, M / (b * N) * ξ i) :=
        mul_le_mul (Finset.sum_le_sum (fun i _ => hcoeff i))
          (Finset.prod_le_prod (fun i _ => mul_nonneg (ha i) (hh i)) (fun i _ => hcoeff i))
          (Finset.prod_nonneg (fun i _ => mul_nonneg (ha i) (hh i)))
          (Finset.sum_nonneg (fun i _ => mul_nonneg hc (hξ i)))
      _ = _ := by
        rw [← Finset.mul_sum, Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_succ]
        ring
  have heq : (∏ i, rateKernel (s i) (a i) / (W i / N)) * (∏ i, ξ i) =
      N ^ r * ∏ i, rateKernel (s i) (a i) * (ξ i / W i) := by
    rw [← Finset.prod_mul_distrib]
    have he (i : Fin r) : rateKernel (s i) (a i) / (W i / N) * ξ i =
        N * (rateKernel (s i) (a i) * (ξ i / W i)) := by
      field_simp
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp
  rw [heq, ← mul_sub, abs_mul, abs_of_pos (pow_pos hN r)]
  calc
    _ ≤ N ^ r * ((∑ i, a i * (ξ i / W i)) * ∏ i, a i * (ξ i / W i)) :=
      mul_le_mul_of_nonneg_left (prod_exponentialGapMass_taylor a s _ ha hs hh) (pow_pos hN r).le
    _ ≤ N ^ r * ((M / (b * N)) ^ (r + 1) * ((∑ i, ξ i) * ∏ i, ξ i)) :=
      mul_le_mul_of_nonneg_left hsp (pow_pos hN r).le
    _ = _ := by ring

/-- The deterministic coefficient in the rescaled error is exactly O(1/N).
All divisions have proved positive denominators. -/
lemma rescaled_gap_error_constant {N b : ℝ} (hN : 0 < N) (hb : 0 < b)
    (M : ℝ) (r : ℕ) :
    (M / (b * N)) ^ (r + 1) * N ^ r = (M / b) ^ (r + 1) / N := by
  rw [div_pow, div_pow, mul_pow, pow_succ N]
  field_simp

end Luce
