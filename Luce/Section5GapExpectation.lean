import Luce.Section3ProfileKernels

/-!
# Expectation transfer for Lemma 5.2

Source: `fixed_points.tex:1035–1048`. The coefficient of a product of
normalized gaps converges in probability. The following quantitative
estimate justifies passing to expectations using a proved second moment.
Its hypotheses are auxiliary analytic hypotheses, to be discharged for
the actual race; they are not a replacement statement of Lemma 5.2.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Luce

set_option backward.isDefEq.respectTransparency false

/-- A bounded error, small off a measurable event, can be multiplied by
an unbounded nonnegative random variable with integrable square. The
truncation parameter `L` is arbitrary and strictly positive. -/
theorem integral_error_mul_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {u Y : Ω → ℝ} {A : Set Ω} (hA : MeasurableSet A)
    (hu : AEStronglyMeasurable u μ) (hY : Integrable Y μ)
    (hY2 : Integrable (fun x => Y x ^ 2) μ)
    (hY0 : ∀ᵐ x ∂μ, 0 ≤ Y x)
    {C ε L : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hL : 0 < L)
    (hbound : ∀ᵐ x ∂μ, |u x| ≤ C)
    (hoff : ∀ᵐ x ∂μ, x ∉ A → |u x| ≤ ε) :
    Integrable (fun x => |u x| * Y x) μ ∧
      (∫ x, |u x| * Y x ∂μ) ≤ ε * (∫ x, Y x ∂μ) +
        C / L * (∫ x, Y x ^ 2 ∂μ) + C * L * μ.real A := by
  have hInt : Integrable (fun x => |u x| * Y x) μ := by
    apply (hY.const_mul C).mono'
    · convert! hu.norm.mul hY.aestronglyMeasurable using 1
    · filter_upwards [hY0, hbound] with x hx hb
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hx)]
      exact mul_le_mul_of_nonneg_right hb hx
  refine ⟨hInt, ?_⟩
  have hind : Integrable (A.indicator (fun _ => C * L)) μ :=
    (integrable_const (C * L)).indicator hA
  have hRight := ((hY.const_mul ε).add (hY2.const_mul (C / L))).add hind
  have hpoint : ∀ᵐ x ∂μ, |u x| * Y x ≤ ε * Y x +
      C / L * Y x ^ 2 + A.indicator (fun _ => C * L) x := by
    filter_upwards [hY0, hbound, hoff] with x hy hub huo
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have hquad : Y x ≤ Y x ^ 2 / L + L := by
        rw [← sub_le_iff_le_add, le_div_iff₀ hL]
        have hs := sq_nonneg (Y x - L)
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hquad hC
      have hεY := mul_nonneg hε hy
      have hmain := mul_le_mul_of_nonneg_right hub hy
      calc
        _ ≤ C * Y x := hmain
        _ ≤ ε * Y x + (C / L * Y x ^ 2 + C * L) := by
          have he : C * (Y x ^ 2 / L + L) = C / L * Y x ^ 2 + C * L := by ring
          rw [he] at hmul
          linarith
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hx]
      have hmain := mul_le_mul_of_nonneg_right (huo hx) hy
      have hn := mul_nonneg (div_nonneg hC hL.le) (sq_nonneg (Y x))
      linarith
  have hi := integral_mono_ae hInt hRight hpoint
  simp only [Pi.add_apply] at hi
  have hsum : Integrable (fun x => ε * Y x + C / L * Y x ^ 2) μ :=
    (hY.const_mul ε).add (hY2.const_mul (C / L))
  rw [integral_add hsum hind,
    integral_add (hY.const_mul ε) (hY2.const_mul (C / L)),
    integral_const_mul, integral_const_mul, integral_indicator_const _ hA,
    smul_eq_mul, mul_comm (μ.real A) (C * L)] at hi
  exact hi

/-- Uniform expectation transfer on varying probability spaces and varying
finite configurations. The moment assumptions are explicitly stated and
will be supplied by the exact selected-gap law, not inferred from weak
convergence. This lemma is only an analytic step toward Lemma 5.2. -/
theorem uniform_integral_error_mul_small
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    {ι : ℕ → Type*} (u Y : (n : ℕ) → ι n → Ω n → ℝ)
    (hu : ∀ n i, Measurable (u n i))
    (hY : ∀ n i, Integrable (Y n i) (μ n))
    (hY2 : ∀ n i, Integrable (fun x => Y n i x ^ 2) (μ n))
    (hY0 : ∀ n i, ∀ᵐ x ∂μ n, 0 ≤ Y n i x)
    (hEY : ∀ n i, (∫ x, Y n i x ∂μ n) = 1)
    {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hEV : ∀ n i, (∫ x, Y n i x ^ 2 ∂μ n) ≤ V)
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ i, ∀ᵐ x ∂μ n, |u n i x| ≤ C)
    (hprob : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ i,
        (μ n).real {x | δ ≤ |u n i x|} < η) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ i,
      (∫ x, |u n i x| * Y n i x ∂μ n) < ε := by
  intro ε hε
  let L : ℝ := 4 * (C + 1) * (V + 1) / ε
  have hCp : 0 < C + 1 := by linarith
  have hVp : 0 < V + 1 := by linarith
  have hL : 0 < L := div_pos (by positivity) hε
  have hδ : 0 < ε / 4 := by positivity
  have hη : 0 < ε / (4 * (C + 1) * L) := by positivity
  filter_upwards [hbound, hprob (ε / 4) hδ _ hη] with n hn hp i
  have hA : MeasurableSet {x | ε / 4 ≤ |u n i x|} := by
    simpa only [Real.norm_eq_abs] using
      measurableSet_le measurable_const (hu n i).norm
  have hoff : ∀ᵐ x ∂μ n, x ∉ {x | ε / 4 ≤ |u n i x|} → |u n i x| ≤ ε / 4 :=
    Eventually.of_forall fun x hx => le_of_lt (lt_of_not_ge hx)
  have hi := (integral_error_mul_le hA (hu n i).aestronglyMeasurable
    (hY n i) (hY2 n i) (hY0 n i) hC hδ.le hL (hn i) hoff).2
  rw [hEY n i, mul_one] at hi
  have hsecond : C / L * (∫ x, Y n i x ^ 2 ∂μ n) ≤ ε / 4 := by
    calc
      _ ≤ C / L * V := mul_le_mul_of_nonneg_left (hEV n i) (div_nonneg hC hL.le)
      _ ≤ (C + 1) / L * (V + 1) := by
        gcongr <;> linarith
      _ = ε / 4 := by
        dsimp [L]
        field_simp
  have hlast : C * L * (μ n).real {x | ε / 4 ≤ |u n i x|} < ε / 4 := by
    calc
      _ ≤ (C + 1) * L * (μ n).real {x | ε / 4 ≤ |u n i x|} := by
        gcongr
        linarith
      _ < (C + 1) * L * (ε / (4 * (C + 1) * L)) :=
        mul_lt_mul_of_pos_left (hp i) (mul_pos hCp hL)
      _ = ε / 4 := by field_simp
  linarith

/-- Subtracting a deterministic target from a coefficient inside an
expectation is legitimate because the normalized gap product has mean one.
Integrability of both terms is explicit. -/
lemma abs_integral_coefficient_mul_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F Y : Ω → ℝ} {B : ℝ}
    (hFY : Integrable (fun x => F x * Y x) μ) (hY : Integrable Y μ)
    (hY0 : ∀ᵐ x ∂μ, 0 ≤ Y x) (hEY : (∫ x, Y x ∂μ) = 1) :
    |(∫ x, F x * Y x ∂μ) - B| ≤ ∫ x, |F x - B| * Y x ∂μ := by
  have he : B = ∫ x, B * Y x ∂μ := by rw [integral_const_mul, hEY, mul_one]
  calc
    _ = |∫ x, F x * Y x - B * Y x ∂μ| := by
      rw [integral_sub hFY (hY.const_mul B), ← he]
    _ ≤ ∫ x, |F x * Y x - B * Y x| ∂μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => F x * Y x - B * Y x)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hY0] with x hx
      rw [← sub_mul, abs_mul, abs_of_nonneg hx]

end Luce
