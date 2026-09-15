import Luce.Section4ApprovedRankIntegral
import Luce.Section4EndpointRace

/-! # Section 7: independent clocks with densities

`Fin n` label `i` means manuscript label `i.val + 1`. Densities are
nonnegative measurable functions of total Lebesgue integral one; no
exponential form or restriction to positive clock times is imposed.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace Luce.Section7

noncomputable section

/-- A real probability density, with its defining analytic properties. -/
structure ClockDensity where
  density : ℝ → ℝ
  measurable : Measurable density
  nonneg : ∀ t, 0 ≤ density t
  integrable : Integrable density
  integral_one : ∫ t, density t = 1

def ClockDensity.law (g : ClockDensity) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (g.density t))

instance (g : ClockDensity) : IsProbabilityMeasure g.law := by
  constructor
  rw [ClockDensity.law, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal g.integrable
      (Filter.Eventually.of_forall g.nonneg), g.integral_one]
  simp

instance (g : ClockDensity) : NullSingletonClass g.law := by
  unfold ClockDensity.law
  infer_instance

def clockRace {n : ℕ} (g : Fin n → ClockDensity) : Measure (Fin n → ℝ) :=
  Measure.pi fun i => (g i).law

instance {n : ℕ} (g : Fin n → ClockDensity) : IsProbabilityMeasure (clockRace g) := by
  unfold clockRace
  infer_instance

def survival {n : ℕ} (g : Fin n → ClockDensity) (i : Fin n) (t : ℝ) : ℝ :=
  (g i).law.real (Ioi t)

/-- The manuscript's `S(t)`. -/
def survivorMean {n : ℕ} (g : Fin n → ClockDensity) (t : ℝ) : ℝ :=
  ∑ i, survival g i t

def survivorProbability {n : ℕ} (g : Fin n → ClockDensity)
    (i : Fin n) (m : ℕ) (t : ℝ) : ℝ :=
  (clockRace g).real {e | otherSurvivors e i t = m}

/-- Terminal label `k_m = n-m+1`, expressed with zero-based labels.
Values outside `1 ≤ m ≤ n` are irrelevant to the terminal sum. -/
def terminalLabel (n : ℕ) (hn : 0 < n) (m : ℕ) : Fin n :=
  ⟨min (n - m) (n - 1), lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

lemma terminalLabel_val {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m) :
    (terminalLabel n hn m).val = n - m := by
  simp only [terminalLabel, Fin.val_mk, min_eq_left (by omega : n - m ≤ n - 1)]

/-- The positive universal constant used in Proposition 7.1. -/
def tailConstant : ℝ := bernoulliLowerTailConstant / 2

theorem tailConstant_pos : 0 < tailConstant :=
  div_pos bernoulliLowerTailConstant_pos (by norm_num)

end
end Luce.Section7
