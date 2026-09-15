import Luce.PredictableProbability
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Martingale.Basic

/-! # Proposed finite compensator statement, Section 2

Source: `fixed_points.tex:581-584`, `eq:compensator-measure`, together with
`eq:fixed-process` at line 150 and the full Luce law at line 142. The paper
uses the state space `[0,1]` at line 269; the proposed real-line measures
therefore have explicit zero-mass-outside-`[0,1]` conclusions below.

The formulas below are proposed definitions. `CompensatorStatement` is an
unasserted proposition: no proof of the compensator claim is provided.
The only proof in this proposal packages the existing exact draw history
as a filtration, using its elementary monotonicity and proved inclusion.
-/

open MeasureTheory
open scoped BigOperators
universe u

namespace Luce.Section2CompensatorProposal

/-- The paper's spatial point `(k.val + 1) / n`, with zero-based `Fin` labels. -/
noncomputable def spatialPoint {n : ℕ} (k : Fin n) : ℝ :=
  ((k.val + 1 : ℕ) : ℝ) / (n : ℝ)

/-- The paper's rank-based fixed-point indicator. -/
def fixedPointIndicator {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) : ℝ :=
  if σ.symm k = k then 1 else 0

/-- Fixed-point atoms observed after `m` draws. The process is constant for
`m ≥ n`, since only positions in `Fin n` occur. -/
noncomputable def fixedPointMeasurePrefix {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) (ω : Ω) : Measure ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < m),
    ENNReal.ofReal (fixedPointIndicator (π ω) k) • Measure.dirac (spatialPoint k)

/-- Cumulative proposed compensator atoms after `m` draws, using the explicit
probabilities from the approved conditional-probability theorem. -/
noncomputable def compensatorMeasurePrefix {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) (ω : Ω) : Measure ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < m),
    ENNReal.ofReal (predictableChance w (π ω) k) • Measure.dirac (spatialPoint k)

/-- The manuscript's terminal fixed-point measure `Ξ_n`. -/
noncomputable def fixedPointMeasure {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (ω : Ω) : Measure ℝ :=
  fixedPointMeasurePrefix π n ω

/-- The manuscript's terminal compensator measure `A_n`. -/
noncomputable def compensatorMeasure {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (ω : Ω) : Measure ℝ :=
  compensatorMeasurePrefix w π n ω

/-- A structure wrapper whose sigma algebra at `m` is definitionally the
approved `drawHistory π m`. No larger or completed history is substituted. -/
def drawFiltration {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π) : Filtration ℕ mΩ where
  seq := drawHistory π
  mono' := by
    intro a b hab
    unfold drawHistory
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    exact le_iSup_of_le j (le_iSup_of_le (lt_of_lt_of_le hj hab) le_rfl)
  le' := drawHistory_le π hπ

/-- Integration of a deterministic spatial test against the cumulative
fixed-point measure. -/
noncomputable def testedFixedPoint {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (g : ℝ → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∫ x, g x ∂fixedPointMeasurePrefix π m ω

/-- Integration of a deterministic spatial test against the cumulative
compensator. Integrability is to follow from the finite deterministic support. -/
noncomputable def testedCompensator {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (g : ℝ → ℝ)
    (m : ℕ) (ω : Ω) : ℝ :=
  ∫ x, g x ∂compensatorMeasurePrefix w π m ω

/-- The cumulative tested fixed-point process centered by its compensator. -/
noncomputable def centeredTestedProcess {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (g : ℝ → ℝ)
    (m : ℕ) (ω : Ω) : ℝ :=
  testedFixedPoint π g m ω - testedCompensator w π g m ω

/-- Proposed exact finite random-measure and tested predictable-compensator
claim. Finiteness, support, measure-valued measurability, spatial and sample
integrability, predictability, and the martingale property are conclusions,
rather than additional model inputs. -/
def CompensatorStatement : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [_hP : IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π),
    (∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ) →
    (∀ (m : ℕ) (ω : Ω),
      IsFiniteMeasure (fixedPointMeasurePrefix π m ω) ∧
      IsFiniteMeasure (compensatorMeasurePrefix w π m ω)) ∧
    (∀ m : ℕ, Measurable (fixedPointMeasurePrefix π m) ∧
      Measurable (compensatorMeasurePrefix w π m)) ∧
    (∀ (m : ℕ) (ω : Ω),
      fixedPointMeasurePrefix π m ω (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      compensatorMeasurePrefix w π m ω (Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧
    ∀ g : ℝ → ℝ, Measurable g →
      (∀ (m : ℕ) (ω : Ω), Integrable g (fixedPointMeasurePrefix π m ω) ∧
        Integrable g (compensatorMeasurePrefix w π m ω)) ∧
      (∀ m : ℕ, Integrable (testedFixedPoint π g m) P ∧
        Integrable (testedCompensator w π g m) P) ∧
      IsStronglyPredictable (drawFiltration π hπ) (testedCompensator w π g) ∧
      Martingale (centeredTestedProcess w π g) (drawFiltration π hπ) P

#print CompensatorStatement
#print axioms CompensatorStatement
#print axioms drawFiltration

end Luce.Section2CompensatorProposal
