import Luce.Section6DeletedSurvival

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Split a nonnegative random starting time at a deterministic threshold.
Integrability follows from boundedness, not from a caller-supplied premise. -/
theorem survival_integral_split {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {S : Ω → ℝ}
    (hS : Measurable S) (hS0 : ∀ᵐ ω ∂μ, 0 ≤ S ω) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    Integrable (fun ω => Real.exp (-a*S ω)) μ ∧
    (∫ ω, Real.exp (-a*S ω) ∂μ) ≤ Real.exp (-a*t)+μ.real {ω | S ω < t} := by
  have hm := Real.measurable_exp.comp ((hS.const_mul (-a)))
  have hi : Integrable (fun ω => Real.exp (-a*S ω)) μ := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [hS0] with ω hω
    change ‖Real.exp (-a*S ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  let A := {ω | S ω < t}
  have hA : MeasurableSet A := measurableSet_lt hS measurable_const
  have hind := (integrable_const (μ := μ) (1 : ℝ)).indicator hA
  have hbound : ∀ᵐ ω ∂μ, Real.exp (-a*S ω) ≤ Real.exp (-a*t)+A.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hS0] with ω hω
    by_cases hωA : ω ∈ A
    · rw [Set.indicator_of_mem hωA]
      have he : Real.exp (-a*S ω) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      linarith [Real.exp_pos (-a*t)]
    · rw [Set.indicator_of_notMem hωA, add_zero]
      apply Real.exp_le_exp.mpr
      have htS : t ≤ S ω := le_of_not_gt hωA
      nlinarith
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, Real.exp (-a*t)+A.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      integral_mono_ae hi ((integrable_const _).add hind) hbound
    _ = _ := by rw [integral_add (integrable_const _) hind, integral_indicator_const _ hA]; simp [A]

/-- Specialization to the original deleted race; nonnegative starting times
are derived almost surely from the clock law. -/
theorem deleted_survival_split {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ) (t : ℝ) :
    (∫ old, Real.exp (-((p : ℝ)*w.rate i*raceGapStart (compactDeletedClocks removed old) q))
      ∂exponentialRace w) ≤ Real.exp (-((p : ℝ)*w.rate i*t))+
      (exponentialRace w).real {old | raceGapStart (compactDeletedClocks removed old) q < t} := by
  have hm := (measurable_raceGapStart q).comp (compactDeletedClocks_measurable removed)
  have hnonneg : ∀ᵐ old ∂exponentialRace w, 0 ≤ raceGapStart (compactDeletedClocks removed old) q := by
    filter_upwards [exponentialRace_injective_ae w, exponentialRace_nonnegative_background w]
      with old hi hn
    rw [raceGapStart_eq_consecutiveGapLower _ (compactDeletedClocks_injective removed old hi)]
    exact consecutiveGapLower_nonneg _ _ (fun j => hn _) q
  simpa only [neg_mul, Function.comp_def] using (survival_integral_split (exponentialRace w) hm hnonneg
    (mul_nonneg (Nat.cast_nonneg p) (w.positive i).le) t).2

end Luce.Section6
