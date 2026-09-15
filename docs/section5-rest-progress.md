# Rest of Section 5: current proof state

The entire revised Section 5 is **complete**, including cycle-shell tightness, joint factorial moments, finite cyclic intensities, arbitrary finite Luce-law realizations, and the full independent-Poisson vector limit in weak convergence and total variation. `Luce.section5_main_general` proves the full result, and `section5_contractCheck` proves the independently frozen closed contract with no external parameters.

The authoritative final statements, assumption diff, axiom output, build results, and gap audit are in [section5-final-report.md](section5-final-report.md). The default build passed (3893 jobs), all 18 final transitive axiom reports use only the allowed foundations, and every frozen hash is unchanged. The milestone entries below are a historical record; their statements about work remaining are superseded by that final report.

## Frozen theorem contract

`ShellMigrationContract.section5` in `Luce/Section5ShellContract.lean` universally quantifies all model data and uses exactly normalization, profile convergence, the raw shell condition, and the defining finite Luce law. Its conclusions include integrability and nonnegativity of every literal cyclic intensity, weak convergence of the actual cycle-count vector, and total variation to the product of the Poisson laws. No tightness or moment result is an input.

The recursive input/type and conclusion audit is `docs/section5-shell-assumption-audit.md`. The raw definitions and existing dependencies are frozen in `audit/section5-contract-freeze.json`. The original Section 4 freeze also remains intact. The completed `section5_contractCheck` is in `Luce/Section5ShellContractCheck.lean` and is imported by the default root build.

## Historical proof milestones

- `cyclicProfileMeasure_eq_closed_cube` and `cycleTraceIntensity_eq_manuscript` identify the contract's product-profile integral exactly with the manuscript's closed-cube Lebesgue integral. No profile regularity or integrability hypothesis is required for this representation identity.
- `cycleMaximum_injective` and `maximumCycleRoots_card` show that every actual cycle has exactly one distinct maximum root. The maximum is constructed from the nonempty finite orbit; it is not an assumed witness.
- `bulkCycleCount_eq_maximum_roots` and `tailCycleCount_eq_maximum_roots` identify the original cutoff count and its exact complement with counts of these roots. The natural subtraction is justified by a finite partition.
- `mem_maximumCycleRoots_iff` characterizes the root event by the actual period and the maximum of the actual orbit.
- `tailCycleExpectation_eq_maximum_probability_sum` proves that the expected terminal cycle count is the sum of the actual maximum-root event probabilities on any probability space carrying a measurable finite permutation. There is no shell or probability bound assumed in this identity.

These extend the previously proved global high-rate truncation, fixed-interior low-rate truncation, and marked-return/marked-edge bounds. The Section 4 closed contract remains proved.

## Maximum-root probability bridge

This bridge is now proved in `Section5MaximumCylinder`, `Section5MaximumReturn`, and `Section5MaximumReturnExpectation`. The event is identified with the actual maximum-root event restricted to a retained set. `retained_maximum_cycle_probability_le_ghost` preserves every other label's strict inequality below the root. `retained_maximum_cycle_probability_le_return` then bounds its probability by the integrated marked edge times the unrestricted return-path weight, keeping the predecessor retained and strictly below the root. Integrability is proved from finite sums of existing ghost-cylinder products.

## Earlier next proof obligation (now resolved)

Full cycle-shell expectation tightness is now proved for every finite collection of lengths, using the original counts and exactly normalization, profile convergence, and the raw shell condition. All bulk joint factorial expectations and actual joint point probabilities converge to their independent-Poisson values. Full cyclic-density integrability, nonnegative full intensities, and convergence of truncated to full intensities are also proved. The next obligations are spatial cutoff removal for the point probabilities, countable-space vector total variation and bounded-test convergence, and transport to arbitrary probability spaces with the finite Luce law. The original closed Section 5 main contract remains unchanged and unproved.

The joint factorial-moment passage to bulk point probabilities is complete. Spatial cutoff removal and joint weak/TV completion remain unproved. All are listed in the obligation ledger. No source contradiction has been found; the gaps are unfinished formal proofs. No missing proposition has been introduced as an assumed structure, instance, axiom, or additional main-theorem hypothesis.

## Validation artifacts

- Default build: `audit/section5-rest-build.log`.
- Closed contract elaboration and transitive axiom audit of completed representation/root results: `audit/section5-contract-and-roots.log`, generated by `audit/Section5ContractAndRoots.lean`.
- Semantic freeze comparison: `audit/section5-freeze-check.json`.

The axiom audit of completed helpers does not certify the still-unproved main theorem or a nonexistent contract check.

Latest commands and actual results:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3833 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5ContractAndRoots.lean
# Exit 0: closed contract elaborated; nine completed-result axiom reports.
python audit/validate_section5_contract_roots.py
# Exit 0: all nine dependencies use only propext, Classical.choice, Quot.sound.
# Original freeze: 162 unchanged files. Section 5 freeze: 193 unchanged files.
```

The initial extraction script needed correction to accept Lean's multiline formatting of a long axiom list. The whitelist was not changed; the final parser checks all names in each complete list. No proof or Lean checking setting was changed to address that output-format issue.

Maximum-root probability continuation validation:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3836 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5MaximumCylinder.lean
# Exit 0: exact elaborated probability bounds and eight transitive axiom reports.
```

Logs are `audit/section5-maximum-full-build.log` and `audit/section5-maximum-cylinder-audit.log`. The exact axiom reports are extracted in `audit/section5-maximum-cylinder-axioms.txt`: all eight contain only `propext`, `Classical.choice`, and `Quot.sound`. Both frozen snapshots remain unchanged (162 and 193 files). The new probability bounds are on the default build path. Neither the Section 5 main theorem nor `section5_contractCheck` is claimed complete by these checks.

## Early-tail and late-source continuation

The actual early part is now complete: `earlyGhostKernel` is the literal ghost probability restricted to times at or below the cutoff, with the original zero extension on tied backgrounds. `ghostEntry_eq_early_add_late` proves the partition identity. `earlyGhostKernel_ae_eq_count` proves the measurable count representation agrees with that literal probability almost surely. `integrable_early_return_product` proves integrability rather than assuming it. `early_ghost_return_expectation` proves the bound for cycle length `l=k+2`, and `earlyCycleShellTail_limit` sums it using the already proved summability of `exp(1-sqrt(j))`. Only normalization is an array assumption for this early part.

For late times, `predecessor_shell_buffer_le` proves the cutoff order from the retained condition `u<v`. `EndpointShellAssumption.eventually_buffered_floor_gt_one` derives the density threshold from the raw shell condition, with the shell cutoff chosen before the eventual row index. `late_marked_edge_integral` proves the integrated scalar-envelope helper, including integrability; `late_source_shell_marked_integral` specializes it to the actual shell minimum. The existing `exponential_density_le` was inspected and reused only as a local scalar lemma: its `gamma` parameter is not a uniform endpoint assumption.

The remaining gap is the combined late-time decomposition and summation for actual retained maximum-root cycles, followed by the high-rate and fixed-interior low-rate truncations in order. The full cycle-shell proposition remains displayed in `docs/shell-obligation-ledger.md`. Joint factorial moments, cyclic-intensity finiteness, joint weak convergence, and vector total variation still require completion. No Section 5 main theorem or contract-checking theorem exists yet. These are unfinished formal proofs; no source contradiction has been established.

Validation commands actually run:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3845 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5EarlyLate.lean
# Exit 0: full statements and fourteen transitive axiom reports.
python audit/validate_section5_early_late.py
# Exit 0: fourteen reports use only propext, Classical.choice, Quot.sound.
# Frozen snapshots: 162 and 193 files; no changed files.
```

The output files are `audit/section5-early-late-build.log`, `audit/section5-early-late-audit.log`, and `audit/section5-early-late-axioms.txt`. The audit prints universes as well as explicit/implicit/instance arguments. The whitelist parser strips only printed universe suffixes, such as `.{u}`, before comparing the exact axiom names. It checks the new central estimates and rechecks the Section 4 generalized main theorem and closed contract check. All nine new production modules are included through imports in the default build. Intermediate elaboration errors were corrected before this successful build; no placeholder declarations remain in these modules.

The fully elaborated main theorem, exact closed Section 4 and Section 5 contracts, and parameter-free Section 4 contract check are printed in the new audit log. The Section 4 assumption diff remains exactly removal of the historical uniform endpoint predicate and addition of the raw shell condition, with no other mathematical input changes. The frozen definitions behind both contracts were unchanged. The audit cannot certify a Section 5 main theorem that has not yet been proved.

## Late decomposition continuation

`late_return_sum_eq_integral` now proves the exact finite sum/integral interchange for the actual late ghost probability. `late_ordered_pairs_le_common_cutoff` keeps `u<v` through the time comparison, then enlarges the nonnegative pair sum. `late_terminal_source_bound` and `late_interior_source_bound` apply this to the two source regions. `finite_cover_sum_le` and `late_retained_pairs_bound` combine the finite source cover. Finally, `late_retained_expectation_bound` transfers that bound to the actual race expectation, proving integrability and discharging the background properties almost surely.

The resulting late bound is `B^l * (exp(-delta*(J-sqrt(J))) + sum_r exp(-b[n,r]*(r-sqrt(r))))`, where the finite sum runs over nonempty source shells from J0 through n. It retains the manuscript's coefficient one in logarithmic time. The new shell-number function is the natural floor of the original real logarithmic depth. Membership in an existing nonempty shell implies equality with this number; the original shell definition is unchanged. The late kernel is the original ghost entry minus its literal early part, and `lateGhostKernel_eq_entry` proves equality to the original late-window probability.

The combined bound is still a local estimate, not the Section 5 main theorem. Its premises have the following status:

| Local premise | Available derivation / remaining application |
| --- | --- |
| Injective, nonnegative background | Discharged almost surely inside `late_retained_expectation_bound`. |
| Late source floor threshold | Derived from the raw shell condition by `eventually_buffered_floor_gt_one`; the final choice of J0 must combine this with small buffered tail cost. |
| Fixed-delta interior threshold | `eventually_interior_density_cutoff` proves it eventually in J. |
| Vanishing interior error | `tendsto_interior_late_error` proves it for every fixed positive delta. |
| Exterior labels belong to source shells | `eventually_exterior_shellNumber` proves this at the fixed spatial cutoff `1-exp(-J0)/2 < 1`, including the rounding buffer. |
| Retained interior rates and discarded cycles | Concrete retained-set selection and its connection to the actual high-rate/interior-low discarded-cycle counts remain to be assembled. |
| Final expected tail-cycle bound | Join the maximum-root probability bound to the early shell sum and the new combined late bound, then discharge all cutoff choices. Unresolved. |

The exact still-unproved cycle-shell proposition is in the obligation ledger. The original joint factorial-moment and joint Poisson/TV completion also remains unproved. There is no Section 5 main theorem or `section5_contractCheck`, and no missing estimate has been added to either frozen contract.

Late decomposition validation commands actually run:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3854 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5LateDecomposition.lean
# Exit 0: fully elaborated new definitions, combined bounds, and frozen contract.
python audit/validate_section5_late_decomposition.py
# Exit 0: thirteen transitive axiom reports, all using only
# propext, Classical.choice, Quot.sound; 162 and 193 frozen files unchanged.
```

Logs: `audit/section5-late-decomposition-build.log`, `audit/section5-late-decomposition-audit.log`, and the exact extracted axiom output `audit/section5-late-decomposition-axioms.txt`. Nine additional production modules are on the default build path. Their theorem types expose the remaining local finite-cutoff premises; none is advertised as the closed Section 5 theorem. Intermediate elaboration errors were corrected before the successful final build.

## Retained expectation tightness

`EndpointShellAssumption.retained_expectation_tightness` now proves the following result with every helper premise discharged:

```lean
theorem EndpointShellAssumption.retained_expectation_tightness {w : WeightArray}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J₀ : ℕ, 2 ≤ J₀ ∧ ∀ M δ : ℝ, 0 < δ →
      ∃ J : ℕ, J₀ ≤ J ∧ ∀ᶠ n : ℕ in atTop,
        (∫ e, (retainedDeepCycleCount (raceRankPermutation e) (k+1)
          (retainedCycleLabels (w n) M (1 - Real.exp (-(J₀ : ℝ))/2) δ) J : ℝ)
          ∂exponentialRace (w n)) < ε
```

Here the cycle length is k+2. The auxiliary count filters the existing actual maximum roots by deep-shell membership and retention of the entire actual orbit. `retainedDeepCycleCount_expectation` identifies its expectation with the original retained maximum-cycle event probabilities. The original cycle count, probability law, intensities, and convergence definitions are unchanged.

The retained label set has `rate <= M` and requires `rate >= delta` only for labels at most beta*n. `not_mem_retainedCycleLabels` proves that its complement is exactly the union of globally high-rate labels and fixed-interior low-rate labels. `eventually_retained_labels_cover` and `retainedInteriorLabels_rate` discharge the finite cover and rate premises. The raw buffered shell tail and its proved eventual floor threshold choose J0; normalization supplies the early tail; the fixed-delta decay chooses J afterwards. The bound is independent of M, so it can be used after choosing the global high-rate truncation first.

This is a retained-cycle theorem, not the full Section 5 theorem. It has no assumed tail bound, intensity bound, or moment input. To reach full cycle-shell tightness, the next missing finite proposition bounds cycles excluded from this retained count by the existing high-rate and interior-low exceptional-vertex counts, then uses their proved expectation limits. The spatial cutoff comparison and the length-one Section 4 case must be combined with it. The joint factorial-moment, cyclic-intensity, and independent-Poisson/vector-TV completion remains unfinished. The frozen Section 5 contract is still unproved.

Retained-tightness validation commands actually run:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3861 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5RetainedTightness.lean
# Exit 0: full theorem/definition/contract elaboration and ten axiom reports.
python audit/validate_section5_retained.py
# Exit 0: all ten reports use only propext, Classical.choice, Quot.sound.
# Both frozen snapshots unchanged: 162 and 193 files.
```

Actual logs: `audit/section5-retained-build.log`, `audit/section5-retained-audit.log`, and `audit/section5-retained-axioms.txt`. Seven additional production modules are in the default build. The combined retained tightness results have no local analytic bound, cover, or instance supplying a missing estimate among their inputs. Their fully elaborated statements and the concrete finite truncation/count definitions are printed in the audit log. No Section 5 main theorem or closed contract check is claimed by this narrower, explicitly identified intermediate milestone.

## Complete cycle-shell endpoint milestone

The manuscript's full short-cycle shell-tightness proposition is now proved by `EndpointShellAssumption.cycle_shell_tightness`. Its exact source statement is:

```lean
theorem EndpointShellAssumption.cycle_shell_tightness {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) :
    Tendsto (fun α : ℝ => limsup (fun n : ℕ =>
      ∫ e, (∑ k : Fin L, (Section5.cycleCount (raceRankPermutation e) k.val -
        Section5.bulkCycleCount (raceRankPermutation e) α k.val : ℕ) : ℝ)
        ∂exponentialRace (w n)) atTop) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```

The discarded-cycle step charges a root to an excluded vertex in its own orbit. Bounding the orbit by the fixed cycle length gives a harmless fixed factor; it neither changes the tail conclusion nor imposes a rate hypothesis. The excluded vertices split into exactly the two original truncations. Their existing expectation estimates are applied in the order M, J0/beta, delta, J, followed by n. The length-one contribution is bounded by the Section 4 tail count on the proved full-measure set of injective clocks. Finally, a common cutoff handles every length up to L. Before every use of the real limsup, eventual upper boundedness is derived from the epsilon estimate and a zero lower bound is proved.

`ShellMigrationContract.cycleShell` in `Section5CycleShellContract.lean` is an independent closed proposition spelling out this same raw conclusion and exactly normalization, profile, and raw shell inputs. It imports the original mathematical definitions, not the new endpoint implementation. This additional intermediate contract matches the proposition already recorded in the obligation ledger; it does not replace or alter the earlier frozen Section 5 main contract. Its new source snapshot is `audit/section5-cycle-shell-contract-freeze.json`; its original imported mathematical dependencies remain covered by the existing frozen snapshots.

The separate build-path check is:

```lean
theorem cycleShell_contractCheck : ShellMigrationContract.cycleShell := by
  intro w f hnorm hf hend L
  exact hend.cycle_shell_tightness hnorm hf L
```

It has no additional explicit, implicit, or instance parameters. The full Section 5 Poisson/intensity/TV conclusion remains unproved, and `section5_contractCheck` is still absent. The factorial assembly milestone below now connects the exact counting identity and `section5_cyclic_local`, but does not yet factor the limiting integral or prove the Poisson conclusion.

Cycle-shell milestone commands actually run:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3871 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5CycleShell.lean
# Exit 0: full theorem/closed contract elaboration and nine transitive axiom reports.
python audit/validate_section5_cycle_shell.py
# Exit 0: nine allowed-axiom reports; snapshots of 162, 193, and 1 files unchanged.
```

Actual central axiom output:

```text
'Luce.EndpointShellAssumption.cycle_shell_tightness' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'cycleShell_contractCheck' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

The complete outputs are `audit/section5-cycle-shell-build.log`, `audit/section5-cycle-shell-audit.log`, and `audit/section5-cycle-shell-axioms.txt`. All ten new production modules, including the separate closed contract check, are on the default build path. This proves the full endpoint proposition, not merely a theorem conditional on retained-cycle tightness or finite intensity. It does not prove the still-unfinished Section 5 main theorem.

## Checked factorial local-limit milestone

`Section5FactorialExpectation` proves the actual joint falling-factorial expectation equals the rank-cylinder sum with the exact rotational divisor. All integrability and almost-sure rank identifications are discharged. `Section5FactorialLocal` proves that reindexing the block vertices preserves both the spatial cutoff and original cylinder event, then applies the checked cyclic local limit with test function one.

The concrete theorem is `Luce.bulk_factorial_tendsto_canonical_block_integral`. It has exactly normalization and original profile convergence as rate-model assumptions, with positive finite rates inherited from `Weights`. Its remaining arguments select L, the multiplicities m, a positive total vertex count, and alpha < 1. A canonical finite equivalence is constructed internally. The zero-order moment is exactly one by `bulk_factorial_expectation_zero`. No shell assumption is needed for this interior result. No count, intensity, probability law, or frozen definition was changed.

The limiting block integral still must be identified with the product of individual truncated cycle intensities. This is an unresolved proof obligation, not an assumption of a claimed generalized main theorem. The positive-order premise is an index case split, not a lower bound or regularity restriction on model rates.

Actual commands and results:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3873 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5FactorialLocal.lean
# Exit 0: elaborated statements/definitions and seven transitive axiom reports.
python audit/validate_section5_factorial_local.py
# Exit 0: seven allowed reports; snapshots of 162, 193, and 1 files unchanged.
```

All seven declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The literal output, including printed universe suffixes, is preserved in `audit/section5-factorial-local-axioms.txt`; the fully elaborated types are in `audit/section5-factorial-local-audit.log`. The full Section 5 main theorem and its closed contract check remain absent, so there is no main-theorem axiom output to claim.

## Completed bulk joint factorial moments

The previous block-factorization obligation is now proved in `Section5BlockProductMeasure` and `Section5BlockIntegral`. Regrouping coordinates by cycle is measure preserving, and reindexing by the original block permutation preserves the actual density integral. Finite-product Fubini gives the intensity product with exactly the original rotational divisor. No additional mathematical assumptions enter this representation identity.

`bulkCycleTraceIntensity f alpha k` is defined literally as the closed-cube integral of `cycleTraceIntegrand f k` over `cyclicBulkCube (k+1) alpha`, divided by `k+1`. It does not alter `cycleTraceIntensity` or any frozen definition. Its truncated integrability is proved from the original profile hypothesis; its nonnegativity follows from the first-moment limit of nonnegative counts.

The new concrete theorem, with all mathematical arguments shown, is:

```lean
theorem Luce.bulk_joint_factorial_moments
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (m : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell : Fin L, bulkCycleTraceIntensity f α ell.val ^ m ell))
```

The fully elaborated type, including instances, is in `audit/section5-factorial-moments-audit.log`. Positive finite rates are inherited from the unchanged `Weights` type. There is no positive-order premise, indexing witness, integrability input, moment input, or endpoint assumption: the zero-order case and canonical indexing are constructed inside the proof. This is an interior moment theorem, not the full Section 5 conclusion.

Commands actually run:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3876 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5FactorialMoments.lean
# Exit 0: fully elaborated statements and nine transitive axiom reports.
python audit/validate_section5_factorial_moments.py
# Exit 0: nine allowed reports; all three snapshots (162, 193, 1 files) unchanged.
```

Actual central output:

```text
'Luce.bulk_joint_factorial_moments' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Luce.bulk_cycle_first_moment' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Luce.bulk_cycle_trace_integrable' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Luce.bulk_cycle_intensity_nonneg' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

The proof obligations now remaining are the distributional passage to the truncated independent-Poisson vector, finiteness/integrability of the full intensities using the first-moment and endpoint results, endpoint cutoff removal, vector total variation, and transport to every probability space with the prescribed finite Luce law. The frozen main `section5` contract and its still-absent `section5_contractCheck` have not been weakened or replaced by the interior theorem.

## Completed full cyclic intensities

`Section5IntensityBounds` proves monotonicity of the truncated intensities and their uniform Cauchy bound directly from the original count expectations. For any tolerance epsilon, the proved cycle-shell tightness selects alpha < 1 such that, for every beta < 1, `bulkCycleTraceIntensity f beta k - bulkCycleTraceIntensity f alpha k <= epsilon`. No interchange of the two endpoint limits is used. Taking epsilon = 1 proves a uniform bound.

`Section5IntensityFinite` uses increasing closed interior cubes that cover almost every point of the original product-profile measure. Their density integrals are uniformly bounded by the preceding theorem. Local integrability and almost-everywhere nonnegativity are proved from the original profile hypothesis. The resulting theorem is:

```lean
theorem Luce.EndpointShellAssumption.cycle_trace_integrable
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ) :
    Integrable (cycleTraceIntegrand f k) (cyclicProfileMeasure (k+1))
```

`cycle_intensity_nonneg hf k` proves the original real intensity is nonnegative. `EndpointShellAssumption.bulk_intensity_tendsto` proves:

```lean
Tendsto (fun alpha => bulkCycleTraceIntensity f alpha k)
  (𝓝[<] (1 : ℝ)) (𝓝 (cycleTraceIntensity f k))
```

Its only model inputs are normalization, original profile convergence, and the raw shell condition. `cyclicProfileMeasure_restrict_closed_bulk` proves the measure identity used in this cutoff limit. All original intensity, density, and probability definitions are unchanged. The full-integrability assertion in the frozen main Section 5 contract is now available as a completed theorem; its vector-law assertions remain unproved, and no `section5_contractCheck` is claimed.

Actual validation:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3878 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5IntensityFinite.lean
# Exit 0: fully elaborated types/definitions and eight transitive axiom reports.
python audit/validate_section5_intensity_finite.py
# Exit 0: eight allowed reports; all frozen snapshots (162, 193, 1 files) unchanged.
```

Actual central output:

```text
'Luce.EndpointShellAssumption.cycle_trace_integrable' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Luce.cycle_intensity_nonneg' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Luce.EndpointShellAssumption.bulk_intensity_tendsto' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

Full statements are in `audit/section5-intensity-finite-audit.log`; complete axiom output is in `audit/section5-intensity-finite-axioms.txt`. The unresolved work is distributional convergence and its final closed contract check, not a remaining intensity assumption or analytic endpoint bound.

## Finite expansion for the joint point probabilities

`Section5FactorialSieve` proves a finite inclusion-exclusion expansion and a pointwise remainder bound. For an actual natural count n and target q, the approximation is

```text
countSieve q K n = sum_{j=0}^K (-1)^j (n)_{q+j} / (q! j!).
```

`countSieve_error_factorial` bounds its error from the indicator of n=q by `(n)_{q+K+1}/(q! (K+1)!)`. These are unconditional finite counting identities and inequalities, including counts below q. `countVectorSieve_error` bounds the product approximation to a joint point indicator by the product of one plus each coordinate's factorial remainder, minus one. It does not assume independence of cycle counts.

`Section5FactorialPolynomials` proves convergence of expectations of any finite product of signed factorial polynomials from the already-proved bulk joint moments. Every finite-row integrability premise is discharged by `integrable_race_permutation_statistic`. Applying this to the actual cycle counts gives `bulk_count_sieve_expectation_limit`, with limit

```text
product_ell sum_{j=0}^K (-1)^j lambda_ell(alpha)^(q_ell+j) / (q_ell! j!).
```

Its only model assumptions are normalization and the original profile convergence, with alpha < 1. The next unresolved step is to integrate the joint remainder, use the polynomial-limit theorem to compute its limiting bound, prove that bound vanishes as K increases, and identify the exponential series. This will yield joint point-mass convergence without an exponential-moment hypothesis. It has not yet been claimed proved.

Actual validation:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3880 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5FactorialSieve.lean
# Exit 0: elaborated statements and eleven transitive axiom reports.
python audit/validate_section5_factorial_sieve.py
# Exit 0: eleven allowed reports; all 162/193/1 frozen files unchanged.
```

Actual central output:

```text
'Luce.countVectorSieve_error' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Luce.bulk_factorial_polynomial_limit' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Luce.bulk_count_sieve_expectation_limit' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

Fully elaborated types and all outputs are in `audit/section5-factorial-sieve-audit.log` and `audit/section5-factorial-sieve-axioms.txt`. No full Section 5 main theorem or closed `section5_contractCheck` is claimed; vector-law convergence, endpoint cutoff removal, total variation, and arbitrary-law transport remain unfinished.

## Completed actual bulk joint point-probability limit

The previous expansion-cutoff obligation is now proved. `Section5SieveRemainder` integrates the deterministic joint remainder and derives its exact row limit from the already-proved factorial-polynomial theorem. `Section5SieveSeries` proves this limiting remainder tends to zero and evaluates the finite expansions using the exponential series. No exponential moment or uniform moment bound is assumed.

`Section5BulkPointMass` combines these limits with an explicit epsilon argument: the approximation order is fixed before taking the row limit. Every premise of the generic finite-approximation helper is discharged by the concrete cycle theorems. `Section5BulkPointProbability` proves measurability and identifies the original event integral with its actual probability, then identifies the limit with the product Poisson measure.

The concrete result is:

```lean
theorem Luce.bulk_cycle_point_probability_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => (exponentialRace (w n)).real {z | (fun ell =>
      Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q}) atTop
      (𝓝 ((bulkCycleVectorPoissonLaw f α L).real {q}))
```

`bulkCycleVectorPoissonLaw` is literally the finite product of Poisson measures with the truncated manuscript intensities. Their nonnegativity was already proved; no intensity hypothesis is hidden in the conversion to nonnegative real parameters. The theorem includes all q, L=0, and every alpha < 1. It is an interior result and needs no endpoint assumption. No frozen law or count definition was changed.

Actual validation:

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3884 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5BulkPointProbability.lean
# Exit 0: fully elaborated types and twelve transitive axiom reports.
python audit/validate_section5_bulk_point.py
# Exit 0: twelve allowed reports; all 162/193/1 frozen files unchanged.
```

Actual central output:

```text
'Luce.bulk_cycle_point_indicator_limit' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Luce.bulkCycleVectorPoissonLaw_real_singleton' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Luce.bulk_cycle_point_probability_limit' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

The complete statement and definition audit is `audit/section5-bulk-point-audit.log`; full axiom output is `audit/section5-bulk-point-axioms.txt`. The remaining proof path is endpoint cutoff removal at the point-probability level using the proved expectation tightness and intensity convergence, countable-space total variation and bounded-test convergence, and transport to the arbitrary probability spaces in the frozen contract. The full `section5_contractCheck` remains absent and the full theorem remains incomplete.
