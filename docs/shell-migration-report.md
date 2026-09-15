# Shell migration report: Section 4 milestone

**Sections 4 and 5 are proved and pass their frozen closed contract checks.** This file records the Section 4 milestone; the complete subsequent Section 5 theorem, final audit, and resolved obligations are in [section5-final-report.md](section5-final-report.md). Statements below about Section 5 being unfinished describe the earlier milestone and are superseded by that final report.

The generalized theorem is `Luce.Shell.section4_main_poisson_general`. It gives integrability of the literal diagonal density, the full spatial Poisson limit against every bounded continuous point-measure test, and scalar count total-variation convergence. It quantifies arbitrary row probability spaces and measurable permutations with the exact Luce masses. The old uniform-endpoint theorems remain available separately.

## Assumption diff for the proved Section 4 theorem

```text
REMOVED: old uniform endpoint lower-bound assumption
ADDED: exact manuscript shell condition
OTHER MATHEMATICAL INPUT CHANGES: none
```

The full assumption/type audit is `docs/shell-assumption-audit.md`. The closed contract and all definitions it originally imported remain byte-for-byte frozen. The new intensity constructor is proved equal to the historical constructor whenever the uniform condition holds (`Luce.Shell.fullIntensity_eq_uniform`); its equality with the raw measure required by the contract is definitional. Neither intensity finiteness nor tightness is a theorem input.

## Exact theorem statement

The following is the implementation's complete source statement, in namespace `Luce.Shell`. Its **fully elaborated** type, including every implicit and instance parameter, is printed in `audit/shell-statements-and-axioms.log`. That log also prints the expanded contract and recursively inspects the project definitions behind its predicates, law, counts, intensity, and convergence notions.

```lean
theorem section4_main_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))) ∧
    Tendsto (fun n => probabilityTotalVariation (fixedPointCountLaw (P n) (π n) (hπ n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0)
```

## Exact frozen closed contract

```lean
import Luce.EndpointShellDefinitions
import Luce.Section4TotalVariation

/-! Frozen Section 4 target, before implementing any generalized main proof.
This module does not import the generalized implementation. The existential
finite intensity is a CONCLUSION, with its underlying measure fixed exactly.
The existing `fullIntensity` cannot be used here because it takes the old
uniform endpoint proof as an argument. -/

noncomputable section
open Luce MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ENNReal
universe u
namespace ShellMigrationContract

/-- Closed arbitrary-space form of `thm:main-poisson`, source lines 318–332.
There are no ambient mathematical section variables or assumed instances. -/
def section4 : Prop :=
  ∀ (Ω : ℕ → Type u) (mΩ : ∀ n, MeasurableSpace (Ω n))
    (P : ∀ n, @Measure (Ω n) (mΩ n)),
    ∀ (hP : ∀ n, @IsProbabilityMeasure (Ω n) (mΩ n) (P n)),
    letI : ∀ n, MeasurableSpace (Ω n) := mΩ
    letI : ∀ n, IsProbabilityMeasure (P n) := hP
    ∀ (w : WeightArray) (f : ℝ → ℝ),
    NormalizedWeights w → ProfileLimit w f →
    Tendsto (fun J : ℕ => limsup (fun n : ℕ =>
      ∑' j : ℕ, if J ≤ j then shellCost w n j else 0) atTop)
      atTop (𝓝 (0 : ℝ≥0∞)) →
    ∀ (π : ∀ n, Ω n → Equiv.Perm (Fin n))
      (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n)),
    (∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) →
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    ∃ ν : FiniteMeasure (Icc (0 : ℝ) 1),
      (ν : Measure (Icc (0 : ℝ) 1)) =
        (interiorDensityMeasure f 1).map (projIcc 0 1 zero_le_one) ∧
      (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
          (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw ν))) ∧
      Tendsto (fun n => probabilityTotalVariation (fixedPointCountLaw (P n) (π n) (hπ n))
          (poissonProbabilityMeasure (Real.toNNReal
            (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0)

end ShellMigrationContract
```

## Separate closed contract-checking theorem

```lean
theorem section4_contractCheck : ShellMigrationContract.section4 := by
  intro Ω mΩ P hP
  letI : ∀ n, MeasurableSpace (Ω n) := mΩ
  letI : ∀ n, IsProbabilityMeasure (P n) := hP
  intro w f hnorm hf hend π hπ hMass
  have h := Luce.Shell.section4_main_poisson_general Ω P w f hnorm hf hend π hπ hMass
  exact ⟨h.1, Luce.Shell.fullIntensity w f hnorm hf hend, rfl, h.2.1, h.2.2⟩
```

The declaration has no external explicit, implicit, or instance parameters. It is outside any section carrying assumptions. Its complete proof calls the concrete shell theorem and supplies the exact finite intensity as a conclusion. `Luce.lean` imports this audit module, so it is checked by the default build.

## Obligation discharge and proof change

The detailed ledger is `docs/shell-obligation-ledger.md`. The shell proof now uses cutoff `j-sqrt(j)` and bounds each early shell contribution by `exp(1-sqrt(j))` for j at least 4096. This summable envelope follows from the sharp Jensen bound and the concrete block-capacity estimate. It avoids needing a separate distinct-maxima summation lemma and introduces no shell summability assumption: summability of this universal error was proved independently. The Q contribution is exactly the previously proved square-root buffered raw shell sum.

The spatial tail bridge retains the original rank/count definitions and handles the one-label offset with `alpha = 1-exp(-J)/2` for sufficiently large n. Expectation tightness is proved first; probability tightness follows by Markov. Interior expectation comparison and Fatou then yield finite full intensity. The existing interior convergence and terminal approximation arguments complete the spatial and scalar limits, with every endpoint premise discharged by these new proofs.

## Actual axiom output

The following lines are extracted verbatim from a successful Lean audit. The whitelist is exactly `propext`, `Classical.choice`, and `Quot.sound`. The shell main theorem and closed contract check are included, so this checks their full transitive dependencies, not merely newly written declarations.

```text
'ShellMigrationContract.old_fullIntensity_underlying' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.shell_index_le_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.shellFloor_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.shellTailCost_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.shellTailCost_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.endpointShellAssumption_iff_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.meanSurvivors_jensen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.NormalizedWeights.meanSurvivors_jensen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.UniformEndpointAssumption.shell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.integral_capacity_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.integrable_capacity_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.capacity_kernel_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.bernoulli_block_lower_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.removed_survivor_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.sum_fullSurvivorProbability_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.exponentialRace_block_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.block_fixedPoint_expectation_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.block_endpoint_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.EndpointShellAssumption.buffered_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.EndpointShellAssumption.buffered_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.EndpointShellAssumption.buffered_Q_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.section4_full_poisson_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.section4_count_poisson_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.section4_main_poisson_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.shell_survivor_buffer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.shell_early_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.shell_block_expectation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.EndpointShellAssumption.expectation_shells' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.spatial_tail_expectation_le_shells' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.EndpointShellAssumption.expectation_tightness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.EndpointShellAssumption.probability_tightness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.Shell.intensity_test_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.Shell.section4_full_intensity_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.Shell.section4_profileDiagonal_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.Shell.section4_main_poisson_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'section4_contractCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Luce.Shell.fullIntensity_eq_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build and remaining work

Actual commands, exit codes, and logs are recorded in `audit/shell-build-results.md`. The statement/axiom audit and frozen-definition comparison are separate checks; a successful compilation alone is not the basis for the claim above.

Section 5 is not certified by this milestone. Its revised compact low-rate truncation is now proved as `ProfileLimit.interior_low_rate_cycles_vanish`, using normalization and profile convergence alone. Its separate actual statement and axiom audit is `audit/section5-shell-progress.log`. Cycle-shell tightness and the subsequent joint theorem still require proofs. The closed Section 5 main-theorem contract is now frozen as ShellMigrationContract.section5; exact maximum-root counting and expectation identities are also proved. See docs/section5-rest-progress.md for the current remaining obligations. The historical global low-rate argument relies on the uniform endpoint hypothesis and cannot supply the new cycle-shell argument. The factorial-moment/joint Poisson/vector-TV completion was already unfinished. No Section 5 main-theorem completion or main-theorem axiom certificate is claimed.

No substantive error in the frozen Section 4 contract was discovered. The existing interpretation of measurable profile as Lebesgue measurable is preserved, as documented in the assumption audit. No model, probability law, count, density, or convergence definition was weakened.
