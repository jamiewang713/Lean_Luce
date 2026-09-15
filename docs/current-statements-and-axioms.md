# Current Lean statements and axioms

Snapshot: 2026-09-11. Project-owned Lean sources only; dependency libraries under `.lake` are excluded.

This catalog lists every source theorem and lemma (including private helpers), anonymous example, definition, structure, class, inductive type, and instance. Theorem proofs are omitted; their source signatures and documentation are retained. Definitions are shown so that an unasserted `Prop` is not mistaken for a proved theorem. Namespace and shared-variable context is listed per file; source links are authoritative for scope. Compiler-generated declarations are excluded from these source counts.

## Counts

| Area | Files | Theorems/lemmas | Definitions/abbreviations | Structures/classes | Instances | Examples | Axioms/opaque |
|---|---:|---:|---:|---:|---:|---:|---:|
| Luce | 253 | 1432 | 299 | 4 | 18 | 1 | 0 |
| proposals | 4 | 0 | 16 | 0 | 0 | 0 | 0 |
| audit | 32 | 5 | 5 | 0 | 0 | 0 | 0 |

## Axioms and proof status

The [fresh compiler inventory](../audit/all-proved-statements.log) prints the elaborated types and transitive axioms of imported project theorem constants, including private and generated auxiliaries and all three closed contract checks. Its final INVENTORY_TOTAL and INVENTORY_AXIOM_UNION lines record the actual totals and axiom dependencies. Source signatures below retain local variable names; consult the compiler inventory for the complete implicit and instance parameters.

The [reproducible audit](../audit/Sections1To7AllProvedStatements.lean) imports the default Luce library. Mathematical hypotheses in theorem parameters and structure fields are distinct from global axioms. Source declarations in proposals and audit files below are explicitly separate from production results; a definition of Prop is not a proof.

The mathematical standing assumptions are defined in `Luce/Section1Model.lean`, `Luce/Section1Assumptions.lean`, and `Luce/Section4EndpointShellDefinitions.lean`. ProfileAssumption, ProfileLimit, EndpointAssumption, and EndpointShellAssumption are predicates, not declarations asserting their truth. The final migration build passed with 3893 jobs; see [actual build output](../audit/section5-final-build.log).

Both revised Section 4 and Section 5 main theorems and their independent closed contract checks are now proved. This includes the full joint factorial-moment argument, short-cycle Poisson limit, full intensity integrability, and joint total variation. Legacy uniform-endpoint estimates remain separate stronger-case theorems. See [final report](section5-final-report.md) and [completed obligation ledger](shell-obligation-ledger.md).

## File index

- [Luce/Sections1To7.lean](#lucesections1to7lean): 0 declarations
- [Luce/Section4ApprovedRankIntegral.lean](#lucesection4approvedrankintegrallean): 11 declarations
- [Luce/Section1Assumptions.lean](#lucesection1assumptionslean): 8 declarations
- [Luce/Section1Basic.lean](#lucesection1basiclean): 1 declarations
- [Luce/Section2BernoulliCountTightness.lean](#lucesection2bernoullicounttightnesslean): 3 declarations
- [Luce/Section2BernoulliPointMeasure.lean](#lucesection2bernoullipointmeasurelean): 15 declarations
- [Luce/Section2BernoulliProcess.lean](#lucesection2bernoulliprocesslean): 24 declarations
- [Luce/Section2CappedPoisson.lean](#lucesection2cappedpoissonlean): 5 declarations
- [Luce/Section2CompactLaplaceApproximation.lean](#lucesection2compactlaplaceapproximationlean): 4 declarations
- [Luce/Section2CompactLawConvergence.lean](#lucesection2compactlawconvergencelean): 11 declarations
- [Luce/Section2ConditionalProbabilityBasics.lean](#lucesection2conditionalprobabilitybasicslean): 4 declarations
- [Luce/Section2ConvergenceInProbability.lean](#lucesection2convergenceinprobabilitylean): 5 declarations
- [Luce/Section4CountableLawConvergence.lean](#lucesection4countablelawconvergencelean): 3 declarations
- [Luce/Section4CountableTotalVariation.lean](#lucesection4countabletotalvariationlean): 10 declarations
- [Luce/Section4DiscreteTotalVariation.lean](#lucesection4discretetotalvariationlean): 13 declarations
- [Luce/Section2DrawHistory.lean](#lucesection2drawhistorylean): 1 declarations
- [Luce/Section2DrawHistoryPermutation.lean](#lucesection2drawhistorypermutationlean): 1 declarations
- [Luce/Section3EmpiricalRace.lean](#lucesection3empiricalracelean): 24 declarations
- [Luce/Section4EndpointEstimates.lean](#lucesection4endpointestimateslean): 10 declarations
- [Luce/Section4EndpointAsymptotic.lean](#lucesection4endpointasymptoticlean): 10 declarations
- [Luce/Section4EndpointBlockCapacity.lean](#lucesection4endpointblockcapacitylean): 4 declarations
- [Luce/Section4EndpointBlockExpectation.lean](#lucesection4endpointblockexpectationlean): 2 declarations
- [Luce/Section4EndpointBlockIntegral.lean](#lucesection4endpointblockintegrallean): 1 declarations
- [Luce/Section4EndpointCapacityAnalytic.lean](#lucesection4endpointcapacityanalyticlean): 11 declarations
- [Luce/Section4EndpointCapacityChernoff.lean](#lucesection4endpointcapacitychernofflean): 1 declarations
- [Luce/Section4EndpointCapacityProbability.lean](#lucesection4endpointcapacityprobabilitylean): 3 declarations
- [Luce/Section4EndpointCutoff.lean](#lucesection4endpointcutofflean): 6 declarations
- [Luce/Section4EndpointIntegrals.lean](#lucesection4endpointintegralslean): 4 declarations
- [Luce/Section4EndpointJensen.lean](#lucesection4endpointjensenlean): 2 declarations
- [Luce/Section4EndpointProbability.lean](#lucesection4endpointprobabilitylean): 7 declarations
- [Luce/Section4EndpointRace.lean](#lucesection4endpointracelean): 16 declarations
- [Luce/Section4EndpointShellBuffer.lean](#lucesection4endpointshellbufferlean): 5 declarations
- [Luce/Section4EndpointShellBufferLimit.lean](#lucesection4endpointshellbufferlimitlean): 8 declarations
- [Luce/Section4EndpointShellCompatibility.lean](#lucesection4endpointshellcompatibilitylean): 3 declarations
- [Luce/Section4EndpointShellCover.lean](#lucesection4endpointshellcoverlean): 2 declarations
- [Luce/Section4EndpointShellDefinitions.lean](#lucesection4endpointshelldefinitionslean): 7 declarations
- [Luce/Section4EndpointShellEarly.lean](#lucesection4endpointshellearlylean): 2 declarations
- [Luce/Section4EndpointShellEstimate.lean](#lucesection4endpointshellestimatelean): 2 declarations
- [Luce/Section4EndpointShellExpectationLimit.lean](#lucesection4endpointshellexpectationlimitlean): 4 declarations
- [Luce/Section4EndpointShellGeometry.lean](#lucesection4endpointshellgeometrylean): 6 declarations
- [Luce/Section4EndpointShells.lean](#lucesection4endpointshellslean): 17 declarations
- [Luce/Section4EndpointShellTailBridge.lean](#lucesection4endpointshelltailbridgelean): 2 declarations
- [Luce/Section4EndpointShellTightness.lean](#lucesection4endpointshelltightnesslean): 4 declarations
- [Luce/Section4EndpointTheorem.lean](#lucesection4endpointtheoremlean): 6 declarations
- [Luce/Section4ExponentialFacts.lean](#lucesection4exponentialfactslean): 5 declarations
- [Luce/Section3ExponentialMemoryless.lean](#lucesection3exponentialmemorylesslean): 1 declarations
- [Luce/Section4ExponentialRace.lean](#lucesection4exponentialracelean): 12 declarations
- [Luce/Section2FiniteAdaptedBernoulli.lean](#lucesection2finiteadaptedbernoullilean): 20 declarations
- [Luce/Section2FiniteBernoulliRow.lean](#lucesection2finitebernoullirowlean): 14 declarations
- [Luce/Section2FiniteBernoulliSpatial.lean](#lucesection2finitebernoullispatiallean): 14 declarations
- [Luce/Section2FiniteHistoryConditional.lean](#lucesection2finitehistoryconditionallean): 4 declarations
- [Luce/Section2FinitePointMeasure.lean](#lucesection2finitepointmeasurelean): 22 declarations
- [Luce/Section2FinitePoissonLaw.lean](#lucesection2finitepoissonlawlean): 21 declarations
- [Luce/Section1FirstChoice.lean](#lucesection1firstchoicelean): 3 declarations
- [Luce/Section2HistoryAtoms.lean](#lucesection2historyatomslean): 5 declarations
- [Luce/Section2HistoryPredictability.lean](#lucesection2historypredictabilitylean): 5 declarations
- [Luce/Section3Interior.lean](#lucesection3interiorlean): 10 declarations
- [Luce/Section4LaplaceCountTightness.lean](#lucesection4laplacecounttightnesslean): 5 declarations
- [Luce/Section2LikelihoodSecondMoment.lean](#lucesection2likelihoodsecondmomentlean): 4 declarations
- [Luce/Section2LuceMassRecursion.lean](#lucesection2lucemassrecursionlean): 5 declarations
- [Luce/Section2LuceNextDraw.lean](#lucesection2lucenextdrawlean): 3 declarations
- [Luce/Section2LucePrefixMass.lean](#lucesection2luceprefixmasslean): 1 declarations
- [Luce/Section2LucePrefixRecursion.lean](#lucesection2luceprefixrecursionlean): 8 declarations
- [Luce/Section2LucePrefixTransition.lean](#lucesection2luceprefixtransitionlean): 4 declarations
- [Luce/Section1Model.lean](#lucesection1modellean): 27 declarations
- [Luce/Section2PointMeasureLaplace.lean](#lucesection2pointmeasurelaplacelean): 17 declarations
- [Luce/Section2PointMeasureLawConvergence.lean](#lucesection2pointmeasurelawconvergencelean): 7 declarations
- [Luce/Section2PoissonCriterion.lean](#lucesection2poissoncriterionlean): 1 declarations
- [Luce/Section2PoissonMixture.lean](#lucesection2poissonmixturelean): 6 declarations
- [Luce/Section2Predictable.lean](#lucesection2predictablelean): 16 declarations
- [Luce/Section2PredictablePoisson.lean](#lucesection2predictablepoissonlean): 1 declarations
- [Luce/Section2PredictableProbability.lean](#lucesection2predictableprobabilitylean): 1 declarations
- [Luce/Section2ProbabilityConvergence.lean](#lucesection2probabilityconvergencelean): 4 declarations
- [Luce/Section3ProfileKernels.lean](#lucesection3profilekernelslean): 24 declarations
- [Luce/Section3ProfileRegularity.lean](#lucesection3profileregularitylean): 5 declarations
- [Luce/Section3RaceConvergence.lean](#lucesection3raceconvergencelean): 4 declarations
- [Luce/Section1RaceOrder.lean](#lucesection1raceorderlean): 11 declarations
- [Luce/Section4RankIntegral.lean](#lucesection4rankintegrallean): 5 declarations
- [Luce/Section4RankIntegralDependencyAudit.lean](#lucesection4rankintegraldependencyauditlean): 0 declarations
- [Luce/Section4RankProbability.lean](#lucesection4rankprobabilitylean): 4 declarations
- [Luce/Section3.lean](#lucesection3lean): 0 declarations
- [Luce/Section3Bernoulli.lean](#lucesection3bernoullilean): 4 declarations
- [Luce/Section3Compensator.lean](#lucesection3compensatorlean): 20 declarations
- [Luce/Section3CompensatorLimit.lean](#lucesection3compensatorlimitlean): 10 declarations
- [Luce/Section3Convergence.lean](#lucesection3convergencelean): 6 declarations
- [Luce/Section3DenominatorReplacement.lean](#lucesection3denominatorreplacementlean): 4 declarations
- [Luce/Section3Expectation.lean](#lucesection3expectationlean): 23 declarations
- [Luce/Section3InitialBlock.lean](#lucesection3initialblocklean): 4 declarations
- [Luce/Section3Intensity.lean](#lucesection3intensitylean): 9 declarations
- [Luce/Section3LuceCompensator.lean](#lucesection3lucecompensatorlean): 5 declarations
- [Luce/Section3LuceLaw.lean](#lucesection3lucelawlean): 1 declarations
- [Luce/Section3Mean.lean](#lucesection3meanlean): 6 declarations
- [Luce/Section3OrderStats.lean](#lucesection3orderstatslean): 9 declarations
- [Luce/Section3Poisson.lean](#lucesection3poissonlean): 11 declarations
- [Luce/Section3PoissonCriterion.lean](#lucesection3poissoncriterionlean): 3 declarations
- [Luce/Section3PoissonLaw.lean](#lucesection3poissonlawlean): 31 declarations
- [Luce/Section3Probability.lean](#lucesection3probabilitylean): 7 declarations
- [Luce/Section3Profile.lean](#lucesection3profilelean): 27 declarations
- [Luce/Section3Quantile.lean](#lucesection3quantilelean): 16 declarations
- [Luce/Section3Race.lean](#lucesection3racelean): 7 declarations
- [Luce/Section3RaceDrawLaw.lean](#lucesection3racedrawlawlean): 5 declarations
- [Luce/Section3RaceLaw.lean](#lucesection3racelawlean): 15 declarations
- [Luce/Section3RemainingWeight.lean](#lucesection3remainingweightlean): 1 declarations
- [Luce/Section3Replacement.lean](#lucesection3replacementlean): 5 declarations
- [Luce/Section3Representations.lean](#lucesection3representationslean): 3 declarations
- [Luce/Section3Survival.lean](#lucesection3survivallean): 6 declarations
- [Luce/Section4.lean](#lucesection4lean): 0 declarations
- [Luce/Section4Approximation.lean](#lucesection4approximationlean): 5 declarations
- [Luce/Section4Compensator.lean](#lucesection4compensatorlean): 3 declarations
- [Luce/Section4Count.lean](#lucesection4countlean): 6 declarations
- [Luce/Section4CountLaw.lean](#lucesection4countlawlean): 8 declarations
- [Luce/Section4Endpoint.lean](#lucesection4endpointlean): 4 declarations
- [Luce/Section4EndpointWitness.lean](#lucesection4endpointwitnesslean): 3 declarations
- [Luce/Section4Fatou.lean](#lucesection4fatoulean): 1 declarations
- [Luce/Section4FullIntensity.lean](#lucesection4fullintensitylean): 7 declarations
- [Luce/Section4Intensity.lean](#lucesection4intensitylean): 13 declarations
- [Luce/Section4IntensityEstimate.lean](#lucesection4intensityestimatelean): 4 declarations
- [Luce/Section4Poisson.lean](#lucesection4poissonlean): 3 declarations
- [Luce/Section4ShellFullIntensity.lean](#lucesection4shellfullintensitylean): 7 declarations
- [Luce/Section4ShellIntensity.lean](#lucesection4shellintensitylean): 4 declarations
- [Luce/Section4ShellIntensityBound.lean](#lucesection4shellintensityboundlean): 2 declarations
- [Luce/Section4ShellPoisson.lean](#lucesection4shellpoissonlean): 3 declarations
- [Luce/Section4ShellTheorem.lean](#lucesection4shelltheoremlean): 2 declarations
- [Luce/Section4ShellTotalVariation.lean](#lucesection4shelltotalvariationlean): 3 declarations
- [Luce/Section4Theorem.lean](#lucesection4theoremlean): 4 declarations
- [Luce/Section4TotalVariation.lean](#lucesection4totalvariationlean): 10 declarations
- [Luce/Section5.lean](#lucesection5lean): 0 declarations
- [Luce/Section5BlockIntegral.lean](#lucesection5blockintegrallean): 4 declarations
- [Luce/Section5BlockProductMeasure.lean](#lucesection5blockproductmeasurelean): 2 declarations
- [Luce/Section5BulkCylinder.lean](#lucesection5bulkcylinderlean): 9 declarations
- [Luce/Section5BulkCylinderAll.lean](#lucesection5bulkcylinderalllean): 4 declarations
- [Luce/Section5BulkPointMass.lean](#lucesection5bulkpointmasslean): 2 declarations
- [Luce/Section5BulkPointProbability.lean](#lucesection5bulkpointprobabilitylean): 6 declarations
- [Luce/Section5ContractDefinitions.lean](#lucesection5contractdefinitionslean): 5 declarations
- [Luce/Section5ContractRepresentation.lean](#lucesection5contractrepresentationlean): 4 declarations
- [Luce/Section5CycleAssignments.lean](#lucesection5cycleassignmentslean): 23 declarations
- [Luce/Section5CycleCutoff.lean](#lucesection5cyclecutofflean): 21 declarations
- [Luce/Section5CycleProbability.lean](#lucesection5cycleprobabilitylean): 14 declarations
- [Luce/Section5Cycles.lean](#lucesection5cycleslean): 37 declarations
- [Luce/Section5CycleShellContract.lean](#lucesection5cycleshellcontractlean): 1 declarations
- [Luce/Section5CycleShellContractCheck.lean](#lucesection5cycleshellcontractchecklean): 1 declarations
- [Luce/Section5CycleShellTightness.lean](#lucesection5cycleshelltightnesslean): 6 declarations
- [Luce/Section5CycleTailLimit.lean](#lucesection5cycletaillimitlean): 5 declarations
- [Luce/Section5CycleTailSmall.lean](#lucesection5cycletailsmalllean): 1 declarations
- [Luce/Section5CyclicAnalytic.lean](#lucesection5cyclicanalyticlean): 44 declarations
- [Luce/Section5CyclicReduction.lean](#lucesection5cyclicreductionlean): 22 declarations
- [Luce/Section5DeletedGaps.lean](#lucesection5deletedgapslean): 14 declarations
- [Luce/Section5DeletedRace.lean](#lucesection5deletedracelean): 17 declarations
- [Luce/Section5DiscardedCycles.lean](#lucesection5discardedcycleslean): 2 declarations
- [Luce/Section5DiscardedLabels.lean](#lucesection5discardedlabelslean): 2 declarations
- [Luce/Section5EarlyDeepSum.lean](#lucesection5earlydeepsumlean): 1 declarations
- [Luce/Section5EarlyExponent.lean](#lucesection5earlyexponentlean): 2 declarations
- [Luce/Section5EarlyKernel.lean](#lucesection5earlykernellean): 7 declarations
- [Luce/Section5EarlyReturn.lean](#lucesection5earlyreturnlean): 1 declarations
- [Luce/Section5EarlyTail.lean](#lucesection5earlytaillean): 5 declarations
- [Luce/Section5EarlyWindowEvent.lean](#lucesection5earlywindoweventlean): 4 declarations
- [Luce/Section5EarlyWindowProbability.lean](#lucesection5earlywindowprobabilitylean): 1 declarations
- [Luce/Section5ExceptionalHigh.lean](#lucesection5exceptionalhighlean): 7 declarations
- [Luce/Section5ExceptionalInteraction.lean](#lucesection5exceptionalinteractionlean): 5 declarations
- [Luce/Section5ExceptionalLow.lean](#lucesection5exceptionallowlean): 6 declarations
- [Luce/Section5FactorialExpectation.lean](#lucesection5factorialexpectationlean): 3 declarations
- [Luce/Section5FactorialLocal.lean](#lucesection5factoriallocallean): 5 declarations
- [Luce/Section5FactorialMoments.lean](#lucesection5factorialmomentslean): 4 declarations
- [Luce/Section5FactorialPolynomials.lean](#lucesection5factorialpolynomialslean): 2 declarations
- [Luce/Section5FactorialSieve.lean](#lucesection5factorialsievelean): 12 declarations
- [Luce/Section5FiniteCover.lean](#lucesection5finitecoverlean): 1 declarations
- [Luce/Section5FiniteInsertion.lean](#lucesection5finiteinsertionlean): 22 declarations
- [Luce/Section5FiniteShellCosts.lean](#lucesection5finiteshellcostslean): 3 declarations
- [Luce/Section5FiniteStatistic.lean](#lucesection5finitestatisticlean): 1 declarations
- [Luce/Section5FiniteTaylor.lean](#lucesection5finitetaylorlean): 7 declarations
- [Luce/Section5FullPointProbability.lean](#lucesection5fullpointprobabilitylean): 4 declarations
- [Luce/Section5GapCoefficient.lean](#lucesection5gapcoefficientlean): 15 declarations
- [Luce/Section5GapCoefficientLimit.lean](#lucesection5gapcoefficientlimitlean): 5 declarations
- [Luce/Section5GapExpectation.lean](#lucesection5gapexpectationlean): 3 declarations
- [Luce/Section5GapLaw.lean](#lucesection5gaplawlean): 37 declarations
- [Luce/Section5GapMoments.lean](#lucesection5gapmomentslean): 8 declarations
- [Luce/Section5GapMomentTransfer.lean](#lucesection5gapmomenttransferlean): 6 declarations
- [Luce/Section5GapProductExpectation.lean](#lucesection5gapproductexpectationlean): 3 declarations
- [Luce/Section5GapReservoir.lean](#lucesection5gapreservoirlean): 4 declarations
- [Luce/Section5GapTaylor.lean](#lucesection5gaptaylorlean): 11 declarations
- [Luce/Section5GhostCylinder.lean](#lucesection5ghostcylinderlean): 16 declarations
- [Luce/Section5GhostTimeSplit.lean](#lucesection5ghosttimesplitlean): 6 declarations
- [Luce/Section5HighRates.lean](#lucesection5highrateslean): 8 declarations
- [Luce/Section5Insertion.lean](#lucesection5insertionlean): 23 declarations
- [Luce/Section5IntensityBounds.lean](#lucesection5intensityboundslean): 6 declarations
- [Luce/Section5IntensityFinite.lean](#lucesection5intensityfinitelean): 10 declarations
- [Luce/Section5InteriorLowRates.lean](#lucesection5interiorlowrateslean): 5 declarations
- [Luce/Section5InteriorWindows.lean](#lucesection5interiorwindowslean): 2 declarations
- [Luce/Section5LateCombined.lean](#lucesection5latecombinedlean): 1 declarations
- [Luce/Section5LateCutoffLimits.lean](#lucesection5latecutofflimitslean): 5 declarations
- [Luce/Section5LateDensity.lean](#lucesection5latedensitylean): 3 declarations
- [Luce/Section5LateKernel.lean](#lucesection5latekernellean): 5 declarations
- [Luce/Section5LateMarkedIntegral.lean](#lucesection5latemarkedintegrallean): 2 declarations
- [Luce/Section5LatePairBound.lean](#lucesection5latepairboundlean): 2 declarations
- [Luce/Section5LateReturnSum.lean](#lucesection5latereturnsumlean): 2 declarations
- [Luce/Section5LateShellGeometry.lean](#lucesection5lateshellgeometrylean): 4 declarations
- [Luce/Section5LateSourceBounds.lean](#lucesection5latesourceboundslean): 3 declarations
- [Luce/Section5Lemma52.lean](#lucesection5lemma52lean): 3 declarations
- [Luce/Section5LowCycleProbability.lean](#lucesection5lowcycleprobabilitylean): 7 declarations
- [Luce/Section5LowCycleRows.lean](#lucesection5lowcyclerowslean): 7 declarations
- [Luce/Section5LowRates.lean](#lucesection5lowrateslean): 5 declarations
- [Luce/Section5LuceTransfer.lean](#lucesection5lucetransferlean): 3 declarations
- [Luce/Section5MarkedCoefficientLimit.lean](#lucesection5markedcoefficientlimitlean): 14 declarations
- [Luce/Section5MarkedExpectation.lean](#lucesection5markedexpectationlean): 2 declarations
- [Luce/Section5MarkedGapBridge.lean](#lucesection5markedgapbridgelean): 9 declarations
- [Luce/Section5MarkedGaps.lean](#lucesection5markedgapslean): 25 declarations
- [Luce/Section5MarkedSort.lean](#lucesection5markedsortlean): 9 declarations
- [Luce/Section5MaximumCylinder.lean](#lucesection5maximumcylinderlean): 5 declarations
- [Luce/Section5MaximumExpectation.lean](#lucesection5maximumexpectationlean): 1 declarations
- [Luce/Section5MaximumReturn.lean](#lucesection5maximumreturnlean): 1 declarations
- [Luce/Section5MaximumReturnExpectation.lean](#lucesection5maximumreturnexpectationlean): 3 declarations
- [Luce/Section5MaximumRoot.lean](#lucesection5maximumrootlean): 11 declarations
- [Luce/Section5MaximumTimeSplit.lean](#lucesection5maximumtimesplitlean): 1 declarations
- [Luce/Section5Microscopic.lean](#lucesection5microscopiclean): 1 declarations
- [Luce/Section5MicroscopicSort.lean](#lucesection5microscopicsortlean): 2 declarations
- [Luce/Section5Occupation.lean](#lucesection5occupationlean): 14 declarations
- [Luce/Section5PointCutoff.lean](#lucesection5pointcutofflean): 3 declarations
- [Luce/Section5Predecessor.lean](#lucesection5predecessorlean): 22 declarations
- [Luce/Section5RaceConclusion.lean](#lucesection5raceconclusionlean): 1 declarations
- [Luce/Section5Resampling.lean](#lucesection5resamplinglean): 9 declarations
- [Luce/Section5Reservoir.lean](#lucesection5reservoirlean): 7 declarations
- [Luce/Section5RetainedExpectation.lean](#lucesection5retainedexpectationlean): 3 declarations
- [Luce/Section5RetainedLabels.lean](#lucesection5retainedlabelslean): 5 declarations
- [Luce/Section5RetainedProbabilityBound.lean](#lucesection5retainedprobabilityboundlean): 1 declarations
- [Luce/Section5RetainedTightness.lean](#lucesection5retainedtightnesslean): 1 declarations
- [Luce/Section5ShellContract.lean](#lucesection5shellcontractlean): 1 declarations
- [Luce/Section5ShellContractCheck.lean](#lucesection5shellcontractchecklean): 1 declarations
- [Luce/Section5ShellCutoff.lean](#lucesection5shellcutofflean): 6 declarations
- [Luce/Section5ShellMain.lean](#lucesection5shellmainlean): 1 declarations
- [Luce/Section5ShellMarkedEdge.lean](#lucesection5shellmarkededgelean): 4 declarations
- [Luce/Section5SieveRemainder.lean](#lucesection5sieveremainderlean): 4 declarations
- [Luce/Section5SieveSeries.lean](#lucesection5sieveserieslean): 4 declarations
- [Luce/Section5SingletonTail.lean](#lucesection5singletontaillean): 3 declarations
- [Luce/Section5TailExpectationBound.lean](#lucesection5tailexpectationboundlean): 1 declarations
- [Luce/Section5VectorTotalVariation.lean](#lucesection5vectortotalvariationlean): 5 declarations
- [Luce/Section5VertexCount.lean](#lucesection5vertexcountlean): 12 declarations
- [Luce/Section5WindowLength.lean](#lucesection5windowlengthlean): 12 declarations
- [Luce/Section5WindowProbability.lean](#lucesection5windowprobabilitylean): 17 declarations
- [Luce/Section4ShellContractCheck.lean](#lucesection4shellcontractchecklean): 2 declarations
- [Luce/Section4ShellContractRepresentation.lean](#lucesection4shellcontractrepresentationlean): 1 declarations
- [Luce/Section4ShellMigrationContract.lean](#lucesection4shellmigrationcontractlean): 1 declarations
- [Luce/Section4ShellMigrationFoundations.lean](#lucesection4shellmigrationfoundationslean): 0 declarations
- [Luce/Section2SpatialPoissonLaplace.lean](#lucesection2spatialpoissonlaplacelean): 2 declarations
- [Luce/Section2Stopping.lean](#lucesection2stoppinglean): 17 declarations
- [Luce/Section4TailAssumptions.lean](#lucesection4tailassumptionslean): 4 declarations
- [Luce/Section4TailCount.lean](#lucesection4tailcountlean): 1 declarations
- [Luce/Section4TailCountIndex.lean](#lucesection4tailcountindexlean): 3 declarations
- [Luce/Section4TailLimit.lean](#lucesection4taillimitlean): 1 declarations
- [Luce/Section4TailProbability.lean](#lucesection4tailprobabilitylean): 5 declarations
- [Luce/Section4TailTightness.lean](#lucesection4tailtightnesslean): 2 declarations
- [Luce/Section4TwoCandidate.lean](#lucesection4twocandidatelean): 4 declarations
- [Luce/Section2UncappedPoisson.lean](#lucesection2uncappedpoissonlean): 2 declarations
- [Luce/Section2WeakMeasureProbability.lean](#lucesection2weakmeasureprobabilitylean): 2 declarations
- [proposals/Section2Compensator.lean](#proposalssection2compensatorlean): 11 declarations
- [proposals/Section2ConditionalProbability.lean](#proposalssection2conditionalprobabilitylean): 1 declarations
- [proposals/Section2Predictability.lean](#proposalssection2predictabilitylean): 2 declarations
- [proposals/Section4TailTightness.lean](#proposalssection4tailtightnesslean): 2 declarations
- [audit/Sections1To7AllProvedStatements.lean](#auditsections1to7allprovedstatementslean): 0 declarations
- [audit/Section1Assumptions.lean](#auditsection1assumptionslean): 0 declarations
- [audit/Section4DiscreteTotalVariation.lean](#auditsection4discretetotalvariationlean): 0 declarations
- [audit/Section2HistoryPredictability.lean](#auditsection2historypredictabilitylean): 4 declarations
- [audit/Section5Lemma52.lean](#auditsection5lemma52lean): 0 declarations
- [audit/Section5Lemma52Proof.lean](#auditsection5lemma52prooflean): 0 declarations
- [audit/Section5Lemma52StatementCheck.lean](#auditsection5lemma52statementchecklean): 0 declarations
- [audit/Section2PoissonCriterion.lean](#auditsection2poissoncriterionlean): 0 declarations
- [audit/Section2PredictableProbability.lean](#auditsection2predictableprobabilitylean): 2 declarations
- [audit/Section5Proposition54.lean](#auditsection5proposition54lean): 0 declarations
- [audit/Section5Proposition54Proof.lean](#auditsection5proposition54prooflean): 0 declarations
- [audit/Section4RankIntegral.lean](#auditsection4rankintegrallean): 0 declarations
- [audit/Section2Existing.lean](#auditsection2existinglean): 0 declarations
- [audit/Section3.lean](#auditsection3lean): 0 declarations
- [audit/Section4.lean](#auditsection4lean): 0 declarations
- [audit/Section4Existing.lean](#auditsection4existinglean): 0 declarations
- [audit/Section5.lean](#auditsection5lean): 0 declarations
- [audit/Section5BulkPointProbability.lean](#auditsection5bulkpointprobabilitylean): 0 declarations
- [audit/Section5ContractAndRoots.lean](#auditsection5contractandrootslean): 0 declarations
- [audit/Section5CycleShell.lean](#auditsection5cycleshelllean): 0 declarations
- [audit/Section5EarlyLate.lean](#auditsection5earlylatelean): 0 declarations
- [audit/Section5FactorialLocal.lean](#auditsection5factoriallocallean): 0 declarations
- [audit/Section5FactorialMoments.lean](#auditsection5factorialmomentslean): 0 declarations
- [audit/Section5FactorialSieve.lean](#auditsection5factorialsievelean): 0 declarations
- [audit/Section5Final.lean](#auditsection5finallean): 0 declarations
- [audit/Section5IntensityFinite.lean](#auditsection5intensityfinitelean): 0 declarations
- [audit/Section5LateDecomposition.lean](#auditsection5latedecompositionlean): 0 declarations
- [audit/Section5MaximumCylinder.lean](#auditsection5maximumcylinderlean): 0 declarations
- [audit/Section5RetainedTightness.lean](#auditsection5retainedtightnesslean): 0 declarations
- [audit/Section5ShellProgress.lean](#auditsection5shellprogresslean): 0 declarations
- [audit/Section4ShellMigrationStatements.lean](#auditsection4shellmigrationstatementslean): 0 declarations
- [audit/Section4TailTightness.lean](#auditsection4tailtightnesslean): 4 declarations

## Luce/Sections1To7.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Sections1To7.lean)

No declarations; imports or audit commands only.


## Luce/Section4ApprovedRankIntegral.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory
namespace Luce
```

### rankOf

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:22)

Approved definition: one plus the number of other clocks ringing earlier.

```lean
noncomputable def rankOf {n : ℕ}
    (e : Fin n → ℝ) (k : Fin n) : ℕ := by
  classical
  exact 1 +
    ((Finset.univ.erase k).filter
      (fun j => e j < e k)).card
```

### otherSurvivors

def; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:30)

Approved definition: the number of other clocks surviving strictly past `t`.

```lean
noncomputable def otherSurvivors {n : ℕ}
    (e : Fin n → ℝ) (k : Fin n) (t : ℝ) : ℕ := by
  classical
  exact ((Finset.univ.erase k).filter
    (fun j => t < e j)).card
```

### rankOf_eq_raceRank

lemma; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:36)

```lean
private lemma rankOf_eq_raceRank {n : ℕ} (e : Fin n → ℝ) (k : Fin n) :
    rankOf e k = raceRank e k
```

### otherSurvivors_eq

lemma; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:42)

```lean
private lemma otherSurvivors_eq {n : ℕ} (e : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    otherSurvivors e k t = ((survivorSet e t).erase k).card
```

### measurable_rankOf

lemma; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:48)

The rank event is measurable as a predicate on a finite clock vector.

```lean
lemma measurable_rankOf {n : ℕ} (k : Fin n) :
    Measurable (fun e : Fin n → ℝ => rankOf e k)
```

### measurable_otherSurvivors

lemma; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:59)

Joint measurability in the deterministic time and the finite clock vector.

```lean
lemma measurable_otherSurvivors {n : ℕ} (k : Fin n) :
    Measurable (fun z : ℝ × (Fin n → ℝ) => otherSurvivors z.2 k z.1)
```

### measurable_otherSurvivors_at

lemma; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:69)

```lean
private lemma measurable_otherSurvivors_at {n : ℕ} (k : Fin n) (t : ℝ) :
    Measurable (fun e : Fin n → ℝ => otherSurvivors e k t)
```

### measurable_survivorProbability_product

lemma; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:73)

```lean
private lemma measurable_survivorProbability_product {n : ℕ}
    (w : Weights n) (k : Fin n) (m : ℕ) :
    Measurable (fun t : ℝ => (exponentialRace w).real
      {e | otherSurvivors e k t = m})
```

### measurable_survivorProbability

lemma; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:84)

The survivor-count probability is measurable in time, derived from the
approved clock hypotheses rather than assumed in the rank integral.

```lean
lemma measurable_survivorProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i)
    (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (E i) (expMeasure (θ i)) P)
    (hIndependent : iIndepFun E P) (k : Fin n) (m : ℕ) :
    Measurable (fun t : ℝ => P.real
      {ω | otherSurvivors (fun i => E i ω) k t = m})
```

### rank_integrand_integrable

theorem; [source line 105](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:105)

Integrability of the exact approved integrand. Its absolute value is
bounded by the exponential density, whose integrability follows from `hθ`.
This obligation is discharged without adding a hypothesis to `rank_integral`.

```lean
theorem rank_integrand_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i)
    (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (E i) (expMeasure (θ i)) P)
    (hIndependent : iIndepFun E P) (k : Fin n) :
    IntegrableOn (fun t : ℝ =>
      θ k * Real.exp (-(θ k * t)) *
        P.real {ω | otherSurvivors (fun i => E i ω) k t = n - (k.val + 1)})
      (Set.Ioi 0)
```

### rank_integral

theorem; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ApprovedRankIntegral.lean:141)

**Locked statement:** `fixed_points.tex`, Lemma `lem:rank-integral`,
equation `eq:rank-integral`. Approved by the user before this proof was written.
The probability space is arbitrary and both probabilities use the same `P`.

```lean
theorem rank_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (n : ℕ)
    (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i)
    (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i,
      ProbabilityTheory.HasLaw
        (E i) (ProbabilityTheory.expMeasure (θ i)) P)
    (hIndependent : ProbabilityTheory.iIndepFun E P)
    (k : Fin n) :
    P.real {ω | rankOf (fun i => E i ω) k = k.val + 1}
      =
    ∫ t in Set.Ioi (0 : ℝ),
      θ k * Real.exp (-(θ k * t)) *
        P.real {ω |
          otherSurvivors (fun i => E i ω) k t
            = n - (k.val + 1)}
```


## Luce/Section1Assumptions.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Assumptions.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
```

### WeightArray

abbrev; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Assumptions.lean:25)

A triangular array of the model's strictly positive weights.

```lean
abbrev WeightArray := (n : ℕ) → Weights n
```

### NormalizedWeights

def; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Assumptions.lean:29)

Mean-one normalization, `eq:normalization`. This is separate from both
numbered assumptions, just as in the manuscript.

```lean
def NormalizedWeights (w : WeightArray) : Prop :=
  ∀ n : ℕ, 0 < n → (1 / (n : ℝ)) * (∑ i : Fin n, (w n).rate i) = 1
```

### stepProfile

def; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Assumptions.lean:36)

The exact step profile of `eq:step-profile`.
The `Fin n` index `i` represents paper label `i.val + 1`, whose cell is
`i.val / n < x ≤ (i.val + 1) / n`. The finite sum is zero outside `(0, 1]`
and on the empty row; neither extension affects the profile limit.

```lean
noncomputable def stepProfile (w : WeightArray) (n : ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ i : Fin n,
    if (i.val : ℝ) / (n : ℝ) < x ∧ x ≤ ((i.val : ℝ) + 1) / (n : ℝ)
    then (w n).rate i else 0
```

### profileMeasure

def; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Assumptions.lean:43)

Lebesgue measure restricted to the profile's domain `(0, 1)`.

```lean
noncomputable def profileMeasure : Measure ℝ :=
  volume.restrict (Set.Ioo (0 : ℝ) 1)
```

### ProfileL1Convergence

def; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Assumptions.lean:50)

The convergence in `eq:L1-profile`, expressed using the extended
nonnegative `L¹` seminorm. Infinite errors remain infinite, rather than taking
the default value of a nonintegrable real Bochner integral. Measurability and
pointwise positivity of the limiting profile belong to Assumption 1.1.

```lean
def ProfileL1Convergence (w : WeightArray) (f : ℝ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => eLpNorm (fun x => stepProfile w n x - f x) 1 profileMeasure)
    atTop (𝓝 0)
```

### ProfileLimit

def; [source line 58](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Assumptions.lean:58)

The limiting profile in Assumption 1.1. `NullMeasurable` expresses the
approved Lebesgue measurability on `(0, 1)`, and positivity is pointwise there.
Values outside the interval are unconstrained. Integrability and unit mass
are not inserted as additional hypotheses.

```lean
def ProfileLimit (w : WeightArray) (f : ℝ → ℝ) : Prop :=
  NullMeasurable f profileMeasure ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x) ∧
    ProfileL1Convergence w f
```

### ProfileAssumption

def; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Assumptions.lean:66)

Assumption 1.1, `ass:profile`, equation `eq:L1-profile`.
There exists a Lebesgue-measurable, pointwise positive limiting profile to
which the step profiles converge in `L¹(0, 1)`.

```lean
def ProfileAssumption (w : WeightArray) : Prop :=
  ∃ f : ℝ → ℝ, ProfileLimit w f
```

### EndpointAssumption

def; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Assumptions.lean:73)

Assumption 1.2, `ass:endpoint`, equation `eq:endpoint-lower`.
One pair of strictly positive constants and one threshold work for all
subsequent rows and every label in the specified closed terminal neighborhood.
No upper bound on `ε₀` is imposed.

```lean
def EndpointAssumption (w : WeightArray) : Prop :=
  ∃ γ ε₀ : ℝ, ∃ n₀ : ℕ,
    0 < γ ∧ 0 < ε₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ k : Fin n,
        (1 - ε₀) * (n : ℝ) ≤ (k.val : ℝ) + 1 →
          γ ≤ (w n).rate k
```


## Luce/Section1Basic.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Basic.lean)

Namespace / shared context (consult source for section boundaries):

```lean
namespace Luce
```

### example at line 12

example; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Basic.lean:12)

```lean
example (n : ℕ) : (Finset.range n).card = n
```


## Luce/Section2BernoulliCountTightness.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliCountTightness.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce.BernoulliProcess
section OneRow
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
section Rows
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
```

### count_tail_le_of_sum_probability_le

theorem; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliCountTightness.lean:25)

Markov's inequality for the observed count, using the predictable
compensator identity and a deterministic cap on that compensator.

```lean
theorem count_tail_le_of_sum_probability_le (N : ℕ) {K R : ℝ} (hR : 0 < R)
    (hK : ∀ ω, ∑ k ∈ Finset.range N, X.probability k ω ≤ K) :
    P.real {ω | R < ∑ k ∈ Finset.range N, X.observation k ω} ≤ K / R
```

### row_bad_event_tendsto_zero

theorem; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliCountTightness.lean:59)

Both fixed-cap failure events have asymptotically vanishing probability.

```lean
theorem row_bad_event_tendsto_zero (X : ∀ n, BernoulliProcess (P n)) (N : ℕ → ℕ)
    {c δ K : ℝ} (hδ : 0 < δ) (hcK : c < K)
    (htotal : ConvergesInProbability P
      (fun n ω => ∑ k ∈ Finset.range (N n), (X n).probability k ω) c)
    (hmax : ConvergesInProbability P (fun n => (X n).rowMaximum (N n)) 0) :
    Tendsto (fun n => (P n).real
      ({ω | δ < (X n).rowMaximum (N n) ω} ∪
        {ω | K < ∑ k ∈ Finset.range (N n), (X n).probability k ω}))
      atTop (𝓝 0)
```

### count_tightness_rows

theorem; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliCountTightness.lean:76)

The finite observation counts are eventually tight under convergence
of the total predictable mass and vanishing maximum individual probability.
The bound is eventual in the row index; no uniform claim for all rows or
expectation bound on the original counts is assumed.

```lean
theorem count_tightness_rows (X : ∀ n, BernoulliProcess (P n)) (N : ℕ → ℕ)
    {c : ℝ} (hc : 0 ≤ c)
    (htotal : ConvergesInProbability P
      (fun n ω => ∑ k ∈ Finset.range (N n), (X n).probability k ω) c)
    (hmax : ConvergesInProbability P (fun n => (X n).rowMaximum (N n)) 0) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ᶠ n in atTop,
      (P n).real {ω | (M : ℝ) < ∑ k ∈ Finset.range (N n), (X n).observation k ω} < ε
```


## Luce/Section2BernoulliPointMeasure.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace Luce
variable {X : Type*} [MeasurableSpace X]
```

### observedPointMeasure

def; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:23)

Retain exactly the points with true Bernoulli observations. The finite
enumeration certifies that the resulting measure is a finite point measure.

```lean
noncomputable def observedPointMeasure {n : ℕ} (x : Fin n → X)
    (b : Fin n → Bool) : FinitePointMeasure X :=
  let s := Finset.univ.filter (fun k => b k)
  FinitePointMeasure.ofFin (fun j : Fin s.card => x (s.equivFin.symm j))
```

### sum_selected_enumeration

lemma; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:28)

```lean
private lemma sum_selected_enumeration {n : ℕ} {A : Type*} [AddCommMonoid A]
    (b : Fin n → Bool) (f : Fin n → A) :
    (let s := Finset.univ.filter (fun k => b k)
     ∑ j : Fin s.card, f (s.equivFin.symm j)) = ∑ k, if b k then f k else 0
```

### observedPointMeasure_toFiniteMeasure

theorem; [source line 39](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:39)

The underlying measure is the literal sum of retained unit Dirac masses.

```lean
theorem observedPointMeasure_toFiniteMeasure {n : ℕ} (x : Fin n → X)
    (b : Fin n → Bool) :
    (observedPointMeasure x b).toFiniteMeasure =
      ∑ k, if b k then (diracProba (x k)).toFiniteMeasure else 0
```

### mass_sum_for_bernoulli

lemma; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:45)

```lean
private lemma mass_sum_for_bernoulli {A : Type*} (s : Finset A) (μ : A → FiniteMeasure X) :
    (∑ i ∈ s, μ i).mass = ∑ i ∈ s, (μ i).mass
```

### observedPointMeasure_mass

theorem; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:59)

The total mass is the number of true observations, including when
several observations occur at the same spatial point.

```lean
theorem observedPointMeasure_mass {n : ℕ} (x : Fin n → X) (b : Fin n → Bool) :
    (observedPointMeasure x b).toFiniteMeasure.mass =
      ∑ k, if b k then (1 : ℝ≥0) else 0
```

### integral_observedPointMeasure

theorem; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:68)

Spatial integration agrees with the literal Bernoulli-weighted sum.

```lean
theorem integral_observedPointMeasure {n : ℕ} (x : Fin n → X) (b : Fin n → Bool)
    (g : X → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂((observedPointMeasure x b).toFiniteMeasure : Measure X)) =
      ∑ k, (if b k then (1 : ℝ) else 0) * g (x k)
```

### pointLaplace_observedPointMeasure

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:81)

The point-measure Laplace test is exactly the exponential used in the
finite-row likelihood argument.

```lean
theorem pointLaplace_observedPointMeasure {n : ℕ} (x : Fin n → X) (b : Fin n → Bool)
    (g : X → ℝ) (hg : Measurable g) :
    pointLaplace g (observedPointMeasure x b) =
      Real.exp (-(∑ k, (if b k then (1 : ℝ) else 0) * g (x k)))
```

### measurable_observedPointMeasure

theorem; [source line 87](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:87)

```lean
theorem measurable_observedPointMeasure {n : ℕ} (x : Fin n → X) :
    Measurable (observedPointMeasure x)
```

### measurable_observedPointMeasure_of_measurable

theorem; [source line 92](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:92)

Coordinate-measurable Bernoulli observations give an actual measurable
random point measure, with no extra regularity imposed on the sample space.

```lean
theorem measurable_observedPointMeasure_of_measurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → X)
    (I : Fin n → Ω → Bool) (hI : ∀ k, Measurable (I k)) :
    Measurable (fun ω => observedPointMeasure x (fun k => I k ω))
```

### weightedPointMeasure

def; [source line 99](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:99)

The literal finite predictable measure with nonnegative coefficients.

```lean
noncomputable def weightedPointMeasure {n : ℕ} (x : Fin n → X)
    (p : Fin n → ℝ≥0) : FiniteMeasure X :=
  ∑ k, p k • (diracProba (x k)).toFiniteMeasure
```

### weightedPointMeasure_mass

theorem; [source line 103](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:103)

```lean
theorem weightedPointMeasure_mass {n : ℕ} (x : Fin n → X) (p : Fin n → ℝ≥0) :
    (weightedPointMeasure x p).mass = ∑ k, p k
```

### integrable_weightedPointMeasure

theorem; [source line 110](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:110)

```lean
theorem integrable_weightedPointMeasure {n : ℕ} (x : Fin n → X) (p : Fin n → ℝ≥0)
    (g : X → ℝ) (hg : Measurable g) :
    Integrable g (weightedPointMeasure x p : Measure X)
```

### integral_weightedPointMeasure

theorem; [source line 118](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:118)

```lean
theorem integral_weightedPointMeasure {n : ℕ} (x : Fin n → X) (p : Fin n → ℝ≥0)
    (g : X → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂(weightedPointMeasure x p : Measure X)) =
      ∑ k, (p k : ℝ) * g (x k)
```

### measurable_weightedPointMeasure

theorem; [source line 129](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:129)

```lean
theorem measurable_weightedPointMeasure {n : ℕ} (x : Fin n → X) :
    Measurable (weightedPointMeasure x)
```

### measurable_weightedPointMeasure_of_measurable

theorem; [source line 140](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliPointMeasure.lean:140)

```lean
theorem measurable_weightedPointMeasure_of_measurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → X)
    (p : Fin n → Ω → ℝ≥0) (hp : ∀ k, Measurable (p k)) :
    Measurable (fun ω => weightedPointMeasure x (fun k => p k ω))
```


## Luce/Section2BernoulliProcess.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped BigOperators
namespace Luce
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
namespace BernoulliProcess
variable {μ} [IsProbabilityMeasure μ] (X : BernoulliProcess μ)
```

### BernoulliProcess

structure; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:21)

An adapted Bernoulli sequence and its predictable compensator atoms.

```lean
structure BernoulliProcess where
  filtration : Filtration ℕ mΩ
  observation : ℕ → Ω → ℝ
  probability : ℕ → Ω → ℝ
  adapted : ∀ k, StronglyMeasurable[filtration (k + 1)] (observation k)
  predictable : ∀ k, StronglyMeasurable[filtration k] (probability k)
  zero_one : ∀ k ω, observation k ω = 0 ∨ observation k ω = 1
  probability_nonneg : ∀ k ω, 0 ≤ probability k ω
  probability_le_one : ∀ k ω, probability k ω ≤ 1
  conditional_mean : ∀ k, μ[observation k | filtration k] =ᵐ[μ] probability k
```

### observation_nonneg

lemma; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:36)

```lean
lemma observation_nonneg (k : ℕ) (ω : Ω) : 0 ≤ X.observation k ω
```

### observation_le_one

lemma; [source line 39](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:39)

```lean
lemma observation_le_one (k : ℕ) (ω : Ω) : X.observation k ω ≤ 1
```

### integrable_observation

lemma; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:42)

```lean
lemma integrable_observation (k : ℕ) : Integrable (X.observation k) μ
```

### integrable_probability

lemma; [source line 47](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:47)

```lean
lemma integrable_probability (k : ℕ) : Integrable (X.probability k) μ
```

### integral_sum_observation

theorem; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:53)

Expected count equals expected compensator mass, without independence.

```lean
theorem integral_sum_observation (N : ℕ) :
    (∫ ω, ∑ k ∈ Finset.range N, X.observation k ω ∂μ) =
      ∫ ω, ∑ k ∈ Finset.range N, X.probability k ω ∂μ
```

### stop

def; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:64)

Predictable deletion according to the two caps from the manuscript.

```lean
noncomputable def stop (δ K : ℝ) : BernoulliProcess μ where
  filtration := X.filtration
  observation k := {ω | keepTerm (fun j => X.probability j ω) δ K k}.indicator
    (X.observation k)
  probability k ω := stoppedProbability (fun j => X.probability j ω) δ K k
  adapted k := (X.adapted k).indicator
    (X.filtration.mono (Nat.le_succ k) _
      (measurableSet_keepTerm X.filtration X.probability
        (fun j => (X.predictable j).measurable) δ K k))
  predictable k := (measurable_stoppedProbability X.filtration X.probability
    (fun j => (X.predictable j).measurable) δ K k).stronglyMeasurable
  zero_one k ω := by
    by_cases h : keepTerm (fun j => X.probability j ω) δ K k
    · simpa [Set.indicator, h] using X.zero_one k ω
    · simp [Set.indicator, h]
  probability_nonneg k ω := stoppedProbability_nonneg (X.probability_nonneg k ω)
  probability_le_one k ω := (stoppedProbability_le (X.probability_nonneg k ω)).trans
    (X.probability_le_one k ω)
  conditional_mean k := by
    have hset := measurableSet_keepTerm X.filtration X.probability
      (fun j => (X.predictable j).measurable) δ K k
    have h := condExp_indicator (X.integrable_observation k) hset
    filter_upwards [h, X.conditional_mean k] with ω hc hm
    rw [hc]
    simp only [Set.indicator, Set.mem_setOf_eq, stoppedProbability]
    split_ifs <;> simp_all
```

### stop_probability_le_cap

lemma; [source line 91](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:91)

```lean
lemma stop_probability_le_cap {δ K : ℝ} (hδ : 0 ≤ δ) (k : ℕ) (ω : Ω) :
    (X.stop δ K).probability k ω ≤ δ
```

### stop_sum_probability_le_cap

lemma; [source line 94](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:94)

```lean
lemma stop_sum_probability_le_cap {δ K : ℝ} (hK : 0 ≤ K) (N : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range N, (X.stop δ K).probability k ω ≤ K
```

### laplaceFactor

def; [source line 102](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:102)

A factor of the likelihood martingale for a nonnegative test function.

```lean
noncomputable def laplaceFactor (g : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.exp (-g * X.observation k ω) /
    (1 - X.probability k ω * (1 - Real.exp (-g)))
```

### laplaceFactor_stronglyMeasurable

lemma; [source line 106](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:106)

```lean
lemma laplaceFactor_stronglyMeasurable (g : ℝ) (k : ℕ) :
    StronglyMeasurable[X.filtration (k + 1)] (X.laplaceFactor g k)
```

### laplaceFactor_bounds

lemma; [source line 112](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:112)

```lean
lemma laplaceFactor_bounds {δ g : ℝ} (hδ : δ < 1) (hg : 0 ≤ g) (k : ℕ) (ω : Ω)
    (hpδ : X.probability k ω ≤ δ) :
    0 ≤ X.laplaceFactor g k ω ∧ X.laplaceFactor g k ω ≤ 1 / (1 - δ)
```

### laplaceFactor_integrable

lemma; [source line 128](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:128)

```lean
lemma laplaceFactor_integrable {δ g : ℝ} (hδ : δ < 1) (hg : 0 ≤ g) (k : ℕ)
    (hpδ : ∀ ω, X.probability k ω ≤ δ) : Integrable (X.laplaceFactor g k) μ
```

### laplaceFactor_conditional_mean

lemma; [source line 135](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:135)

```lean
lemma laplaceFactor_conditional_mean {δ g : ℝ} (hδ : δ < 1) (hg : 0 ≤ g) (k : ℕ)
    (hpδ : ∀ ω, X.probability k ω ≤ δ) :
    μ[X.laplaceFactor g k | X.filtration k] =ᵐ[μ] (fun _ => 1)
```

### likelihood

def; [source line 145](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:145)

Finite likelihood process.

```lean
noncomputable def likelihood (g : ℕ → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range N, X.laplaceFactor (g k) k ω
```

### likelihood_integrable

lemma; [source line 148](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:148)

```lean
lemma likelihood_integrable {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) :
    Integrable (X.likelihood g N) μ
```

### likelihood_martingale

theorem; [source line 164](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:164)

```lean
theorem likelihood_martingale {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hpδ : ∀ k ω, X.probability k ω ≤ δ) :
    Martingale (X.likelihood g) X.filtration μ
```

### integral_likelihood

theorem; [source line 173](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:173)

```lean
theorem integral_likelihood {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) :
    (∫ ω, X.likelihood g N ω ∂μ) = 1
```

### laplaceProduct

def; [source line 183](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:183)

Product of conditional Laplace transforms.

```lean
noncomputable def laplaceProduct (g : ℕ → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range N, (1 - X.probability k ω * (1 - Real.exp (-g k)))
```

### likelihood_eq_laplace_div

lemma; [source line 186](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:186)

```lean
lemma likelihood_eq_laplace_div (g : ℕ → ℝ) (N : ℕ) (ω : Ω) :
    X.likelihood g N ω = Real.exp (-(∑ k ∈ Finset.range N, g k * X.observation k ω)) /
      X.laplaceProduct g N ω
```

### laplaceProduct_bounds

lemma; [source line 192](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:192)

```lean
lemma laplaceProduct_bounds {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) (ω : Ω) :
    0 < X.laplaceProduct g N ω ∧ X.laplaceProduct g N ω ≤ 1
```

### laplaceProduct_integrable

lemma; [source line 204](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:204)

```lean
lemma laplaceProduct_integrable {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) : Integrable (X.laplaceProduct g N) μ
```

### likelihood_mul_laplaceProduct

lemma; [source line 215](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:215)

```lean
lemma likelihood_mul_laplaceProduct {δ : ℝ} (hδ : δ < 1) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) (ω : Ω) :
    X.likelihood g N ω * X.laplaceProduct g N ω =
      Real.exp (-(∑ k ∈ Finset.range N, g k * X.observation k ω))
```

### likelihood_bounds_of_sum_le

lemma; [source line 223](D:/princeton/Research/Lean/Lean_luce/Luce/Section2BernoulliProcess.lean:223)

Uniform bound for the stopped likelihood from its total compensator cap.

```lean
lemma likelihood_bounds_of_sum_le {δ K : ℝ} (hδ : δ < 1) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ) (ω : Ω)
    (hK : ∑ k ∈ Finset.range N, X.probability k ω ≤ K) :
    0 ≤ X.likelihood g N ω ∧ X.likelihood g N ω ≤ Real.exp (K / (1 - δ))
```


## Luce/Section2CappedPoisson.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CappedPoisson.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
namespace BernoulliProcess
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
```

### laplaceCompensator

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CappedPoisson.lean:22)

Compensator tested against `1 - exp(-g)`.

```lean
noncomputable def laplaceCompensator (X : BernoulliProcess μ) (g : ℕ → ℝ)
    (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N, X.probability k ω * (1 - Real.exp (-g k))
```

### laplaceCompensator_integrable

lemma; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CappedPoisson.lean:26)

```lean
lemma laplaceCompensator_integrable (X : BernoulliProcess μ) (g : ℕ → ℝ) (N : ℕ) :
    Integrable (X.laplaceCompensator g N) μ
```

### laplaceCompensator_bounds

lemma; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CappedPoisson.lean:30)

```lean
lemma laplaceCompensator_bounds (X : BernoulliProcess μ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (N : ℕ) (ω : Ω) :
    0 ≤ X.laplaceCompensator g N ω ∧
      X.laplaceCompensator g N ω ≤ ∑ k ∈ Finset.range N, X.probability k ω
```

### integral_laplace_error_of_atom_bound

theorem; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CappedPoisson.lean:42)

Quantitative Laplace error for an adapted Bernoulli array with capped mass.
The factor `a` may depend on the entire outcome; it bounds the largest atom.

```lean
theorem integral_laplace_error_of_atom_bound (X : BernoulliProcess μ)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (N : ℕ) {δ K lam : ℝ} {a : Ω → ℝ}
    (hδ : δ < 1) (hlam : 0 ≤ lam) (haint : Integrable a μ)
    (ha0 : ∀ ω, 0 ≤ a ω) (haδ : ∀ ω, a ω ≤ δ)
    (hp : ∀ k ω, X.probability k ω ≤ a ω)
    (hK : ∀ ω, ∑ k ∈ Finset.range N, X.probability k ω ≤ K) :
    |(∫ ω, Real.exp (-(∑ k ∈ Finset.range N, g k * X.observation k ω)) ∂μ) -
      Real.exp (-lam)| ≤ Real.exp (K / (1 - δ)) *
        (K / (1 - δ) * (∫ ω, a ω ∂μ) +
          ∫ ω, |X.laplaceCompensator g N ω - lam| ∂μ)
```

### capped_laplace_tendsto

theorem; [source line 95](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CappedPoisson.lean:95)

The capped predictable Poisson criterion for a single Laplace test.
Applying this to each nonnegative continuous spatial test gives the Laplace
functional asserted in Lemma `lem:predictable-poisson`.

```lean
theorem capped_laplace_tendsto (X : ℕ → BernoulliProcess μ) (g : ℕ → ℕ → ℝ)
    (N : ℕ → ℕ) {δ K lam : ℝ} (hδ : δ < 1) (hlam : 0 ≤ lam)
    (hg : ∀ n k, 0 ≤ g n k) (a : ℕ → Ω → ℝ)
    (haint : ∀ n, Integrable (a n) μ) (ha0 : ∀ n ω, 0 ≤ a n ω)
    (haδ : ∀ n ω, a n ω ≤ δ)
    (hp : ∀ n k ω, (X n).probability k ω ≤ a n ω)
    (hK : ∀ n ω, ∑ k ∈ Finset.range (N n), (X n).probability k ω ≤ K)
    (hatendsto : TendstoInMeasure μ a atTop (fun _ => 0))
    (hcomp : TendstoInMeasure μ
      (fun n => (X n).laplaceCompensator (g n) (N n)) atTop (fun _ => lam)) :
    Tendsto (fun n => ∫ ω, Real.exp (-(∑ k ∈ Finset.range (N n),
      g n k * (X n).observation k ω)) ∂μ) atTop (𝓝 (Real.exp (-lam)))
```


## Luce/Section2CompactLaplaceApproximation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLaplaceApproximation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open Topology
open Filter
open scoped BoundedContinuousFunction
namespace Luce
```

### continuous_factorsThrough_of_isInducing

lemma; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLaplaceApproximation.lean:23)

A continuous real function is constant on the fibers of a map inducing
the topology. The original space need not be Hausdorff or even `T₀`.

```lean
lemma continuous_factorsThrough_of_isInducing
    {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]
    (J : S → M) (hJ : IsInducing J) (F : C(S, ℝ)) :
    Function.FactorsThrough F J
```

### exists_algebra_approximation_of_isInducing

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLaplaceApproximation.lean:33)

Stone-Weierstrass after descending through a surjective moment map.
The compactness of the image is derived from the source.

```lean
theorem exists_algebra_approximation_of_isInducing
    {S M : Type*} [TopologicalSpace S] [CompactSpace S] [TopologicalSpace M]
    (J : S → M) (hJ : IsInducing J) (hsurj : Function.Surjective J)
    (A : Subalgebra ℝ C(M, ℝ)) (hA : A.SeparatesPoints)
    (F : C(S, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ A, ∀ s : S, ‖a (J s) - F s‖ < ε
```

### exists_algebra_approximation_on_compact_of_isInducing

theorem; [source line 57](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLaplaceApproximation.lean:57)

Approximate a bounded continuous state functional uniformly on a compact
set by an algebra on its moment image. All algebra membership is retained
on the full image space, so the result can be used for Laplace polynomials.

```lean
theorem exists_algebra_approximation_on_compact_of_isInducing
    {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]
    (J : S → M) (hJ : IsInducing J)
    (A : Subalgebra ℝ C(M, ℝ)) (hA : A.SeparatesPoints)
    (F : S →ᵇ ℝ) {K : Set S} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ A, ∀ s ∈ K, ‖a (J s) - F s‖ < ε
```

### measurable_boundedContinuousFunction_of_compact_exhaustion

theorem; [source line 93](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLaplaceApproximation.lean:93)

If the moment algebra is measurable and the state space is exhausted
eventually by compact sets, every bounded continuous real state functional
is measurable. The measurable space is arbitrary: no measurability of all
weak-open sets is needed.

```lean
theorem measurable_boundedContinuousFunction_of_compact_exhaustion
    {S M : Type*} [TopologicalSpace S] [MeasurableSpace S] [TopologicalSpace M]
    (J : S → M) (hJ : IsInducing J)
    (A : Subalgebra ℝ C(M, ℝ)) (hA : A.SeparatesPoints)
    (hAmeas : ∀ a ∈ A, Measurable (fun s => a (J s)))
    (K : ℕ → Set S) (hK : ∀ n, IsCompact (K n))
    (hcover : ∀ s, ∀ᶠ n in atTop, s ∈ K n) (F : S →ᵇ ℝ) :
    Measurable F
```


## Luce/Section2CompactLawConvergence.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction Polynomial
namespace Luce
```

### integral_sub_abs_le_uniform

lemma; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:15)

```lean
lemma integral_sub_abs_le_uniform
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {f g : S → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) {ε : ℝ}
    (hε : ∀ s, |f s - g s| ≤ ε) :
    |(∫ s, f s ∂μ) - ∫ s, g s ∂μ| ≤ ε
```

### tendsto_integral_of_uniform_approximation

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:28)

Convergence of integrals is preserved under global uniform approximation
of a bounded measurable test, even when the source sigma algebra is unrelated
to a topology.

```lean
theorem tendsto_integral_of_uniform_approximation
    {S : Type*} [MeasurableSpace S] (μ : ℕ → Measure S) (ν : Measure S)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hbound : ∀ s, |f s| ≤ B)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : S → ℝ, Measurable g ∧
      (∀ s, |g s - f s| ≤ ε) ∧
      Tendsto (fun n => ∫ s, g s ∂μ n) atTop (𝓝 (∫ s, g s ∂ν))) :
    Tendsto (fun n => ∫ s, f s ∂μ n) atTop (𝓝 (∫ s, f s ∂ν))
```

### exists_algebra_uniform_approximation_comp

theorem; [source line 75](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:75)

Scalar continuous transformations of one bounded algebra element can be
approximated globally by elements of the same algebra.

```lean
theorem exists_algebra_uniform_approximation_comp
    {S M : Type*} [TopologicalSpace M]
    (J : S → M) (A : Subalgebra ℝ C(M, ℝ))
    (a : C(M, ℝ)) (ha : a ∈ A) {B : ℝ} (hbound : ∀ s, |a (J s)| ≤ B)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) {ε : ℝ} (hε : 0 < ε) :
    ∃ b ∈ A, ∀ s, |b (J s) - ψ (a (J s))| < ε
```

### tendsto_integral_continuous_comp_of_subalgebra

theorem; [source line 92](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:92)

A continuous scalar transformation of a bounded algebra test inherits
convergence of expectations from the algebra.

```lean
theorem tendsto_integral_continuous_comp_of_subalgebra
    {S M : Type*} [MeasurableSpace S] [TopologicalSpace M]
    (μ : ℕ → Measure S) (ν : Measure S)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (J : S → M) (A : Subalgebra ℝ C(M, ℝ))
    (hAmeas : ∀ a ∈ A, Measurable (fun s => a (J s)))
    (hAconv : ∀ a ∈ A,
      Tendsto (fun n => ∫ s, a (J s) ∂μ n) atTop (𝓝 (∫ s, a (J s) ∂ν)))
    (a : C(M, ℝ)) (ha : a ∈ A) {B : ℝ} (hbound : ∀ s, |a (J s)| ≤ B)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hψbound : ∀ s, |ψ (a (J s))| ≤ C) :
    Tendsto (fun n => ∫ s, ψ (a (J s)) ∂μ n)
      atTop (𝓝 (∫ s, ψ (a (J s)) ∂ν))
```

### symmetricClip

def; [source line 113](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:113)

Clipping a real number to a symmetric bounded interval.

```lean
def symmetricClip (B x : ℝ) : ℝ := max (-B) (min B x)
```

### continuous_symmetricClip

lemma; [source line 115](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:115)

```lean
lemma continuous_symmetricClip (B : ℝ) : Continuous (symmetricClip B)
```

### abs_symmetricClip_le

lemma; [source line 118](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:118)

```lean
lemma abs_symmetricClip_le {B : ℝ} (hB : 0 ≤ B) (x : ℝ) :
    |symmetricClip B x| ≤ B
```

### symmetricClip_eq_self

lemma; [source line 123](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:123)

```lean
lemma symmetricClip_eq_self {B x : ℝ} (hx : |x| ≤ B) : symmetricClip B x = x
```

### abs_symmetricClip_sub_le

lemma; [source line 127](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:127)

```lean
lemma abs_symmetricClip_sub_le {B x y : ℝ} (hy : |y| ≤ B) :
    |symmetricClip B x - y| ≤ |x - y|
```

### integral_sub_abs_le_on_set

lemma; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:141)

A local uniform approximation controls expectations up to the mass
outside the approximation set.

```lean
lemma integral_sub_abs_le_on_set
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {f g : S → ℝ} (hf : Measurable f) (hg : Measurable g) {B ε : ℝ}
    (hfbound : ∀ s, |f s| ≤ B) (hgbound : ∀ s, |g s| ≤ B) (hε : 0 ≤ ε)
    {K : Set S} (hK : MeasurableSet K) (happrox : ∀ s ∈ K, |f s - g s| ≤ ε) :
    |(∫ s, f s ∂μ) - ∫ s, g s ∂μ| ≤ ε + 2 * B * μ.real Kᶜ
```

### tendsto_integral_boundedContinuousFunction_of_tight_algebra

theorem; [source line 178](D:/princeton/Research/Lean/Lean_luce/Luce/Section2CompactLawConvergence.lean:178)

Convergence on a bounded measurable moment algebra, together with
tightness on compact sets, implies convergence for every bounded continuous
state test. The sigma algebra need not contain every topologically open set.

```lean
theorem tendsto_integral_boundedContinuousFunction_of_tight_algebra
    {S M : Type*} [TopologicalSpace S] [MeasurableSpace S] [TopologicalSpace M]
    (μ : ℕ → Measure S) (ν : Measure S)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (J : S → M) (hJ : IsInducing J)
    (A : Subalgebra ℝ C(M, ℝ)) (hA : A.SeparatesPoints)
    (hAmeas : ∀ a ∈ A, Measurable (fun s => a (J s)))
    (hAbound : ∀ a ∈ A, ∃ B : ℝ, ∀ s, |a (J s)| ≤ B)
    (hAconv : ∀ a ∈ A,
      Tendsto (fun n => ∫ s, a (J s) ∂μ n) atTop (𝓝 (∫ s, a (J s) ∂ν)))
    (K : ℕ → Set S) (hKcompact : ∀ N, IsCompact (K N))
    (hKmeas : ∀ N, MeasurableSet (K N))
    (hcover : ∀ s, ∀ᶠ N in atTop, s ∈ K N)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ N,
      ν.real (K N)ᶜ ≤ ε ∧ ∀ᶠ n in atTop, (μ n).real (K N)ᶜ ≤ ε)
    (F : S →ᵇ ℝ) :
    Tendsto (fun n => ∫ s, F s ∂μ n) atTop (𝓝 (∫ s, F s ∂ν))
```


## Luce/Section2ConditionalProbabilityBasics.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConditionalProbabilityBasics.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
universe u
namespace Luce
```

### drawHistory_le

lemma; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConditionalProbabilityBasics.lean:16)

```lean
lemma drawHistory_le {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π) (m : ℕ) :
    drawHistory π m ≤ mΩ
```

### measurable_predictableChance_history

lemma; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConditionalProbabilityBasics.lean:28)

```lean
lemma measurable_predictableChance_history {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (k : Fin n) :
    Measurable[drawHistory π k.val] (fun ω => predictableChance w (π ω) k)
```

### integrable_predictableChance

lemma; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConditionalProbabilityBasics.lean:35)

```lean
lemma integrable_predictableChance {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π) (k : Fin n) :
    Integrable (fun ω => predictableChance w (π ω) k) P
```

### integrable_fixed_point_indicator

lemma; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConditionalProbabilityBasics.lean:45)

```lean
lemma integrable_fixed_point_indicator {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π) (k : Fin n) :
    Integrable (fun ω => if (π ω).symm k = k then (1 : ℝ) else 0) P
```


## Luce/Section2ConvergenceInProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConvergenceInProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped Topology
namespace Luce
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
namespace ConvergesInProbability
variable {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
```

### ConvergesInProbability

def; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConvergenceInProbability.lean:17)

Convergence in probability to a real constant, allowing varying spaces.

```lean
def ConvergesInProbability (μ : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ε < |X n ω - c|}) atTop (𝓝 0)
```

### mono

theorem; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConvergenceInProbability.lean:25)

```lean
theorem mono (hY : ConvergesInProbability μ Y d)
    (hbound : ∀ n ω, |X n ω - c| ≤ |Y n ω - d|) : ConvergesInProbability μ X c
```

### congr_off

theorem; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConvergenceInProbability.lean:35)

Changing variables on events whose probabilities vanish preserves the limit.

```lean
theorem congr_off (hY : ConvergesInProbability μ Y c) (bad : ∀ n, Set (Ω n))
    (hbad : Tendsto (fun n => (μ n).real (bad n)) atTop (𝓝 0))
    (heq : ∀ n ω, ω ∉ bad n → X n ω = Y n ω) : ConvergesInProbability μ X c
```

### upper_tail

theorem; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConvergenceInProbability.lean:55)

```lean
theorem upper_tail (hX : ConvergesInProbability μ X c) {K : ℝ} (hK : c < K) :
    Tendsto (fun n => (μ n).real {ω | K < X n ω}) atTop (𝓝 0)
```

### integral_abs_tendsto

theorem; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ConvergenceInProbability.lean:65)

Bounded convergence to the deterministic limit in `L¹`.

```lean
theorem integral_abs_tendsto (hX : ConvergesInProbability μ X c)
    (hXmeas : ∀ n, Measurable (X n)) {B : ℝ}
    (hbound : ∀ n ω, |X n ω - c| ≤ B) :
    Tendsto (fun n => ∫ ω, |X n ω - c| ∂μ n) atTop (𝓝 0)
```


## Luce/Section4CountableLawConvergence.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableLawConvergence.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace Luce.CountableLaw
variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
```

### tendsto_event_probability_of_totalVariation

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableLawConvergence.lean:9)

```lean
theorem tendsto_event_probability_of_totalVariation
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (h : Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0)) (A : Set E) :
    Tendsto (fun n => (μ n : Measure E).real A) atTop (𝓝 ((ν : Measure E).real A))
```

### tendsto_probabilityMeasure_of_totalVariation

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableLawConvergence.lean:19)

```lean
theorem tendsto_probabilityMeasure_of_totalVariation
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (h : Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0)) :
    Tendsto μ atTop (𝓝 ν)
```

### tendsto_bounded_integrals_of_totalVariation

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableLawConvergence.lean:28)

```lean
theorem tendsto_bounded_integrals_of_totalVariation
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (h : Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0))
    (F : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, F x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, F x ∂(ν : Measure E)))
```


## Luce/Section4CountableTotalVariation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace Luce.CountableLaw
variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
```

### probabilityTotalVariation

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean:20)

Probability total variation: the supremum over events, with no factor two.

```lean
def probabilityTotalVariation (μ ν : ProbabilityMeasure E) : ℝ :=
  sSup (Set.range fun A : Set E => |(μ : Measure E).real A - (ν : Measure E).real A|)
```

### probability_event_difference_le_one

lemma; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean:23)

```lean
private lemma probability_event_difference_le_one (μ ν : ProbabilityMeasure E)
    (A : Set E) : |(μ : Measure E).real A - (ν : Measure E).real A| ≤ 1
```

### probabilityTotalVariation_nonneg

lemma; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean:35)

```lean
lemma probabilityTotalVariation_nonneg (μ ν : ProbabilityMeasure E) :
    0 ≤ probabilityTotalVariation μ ν
```

### probabilityTotalVariation_le_one

lemma; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean:43)

```lean
lemma probabilityTotalVariation_le_one (μ ν : ProbabilityMeasure E) :
    probabilityTotalVariation μ ν ≤ 1
```

### probability_event_difference_le_totalVariation

lemma; [source line 49](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean:49)

```lean
lemma probability_event_difference_le_totalVariation (μ ν : ProbabilityMeasure E)
    (A : Set E) :
    |(μ : Measure E).real A - (ν : Measure E).real A| ≤ probabilityTotalVariation μ ν
```

### probability_finite_event_difference_le

lemma; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean:55)

```lean
private lemma probability_finite_event_difference_le (μ ν : ProbabilityMeasure E)
    (s : Finset E) (A : Set E) :
    |(μ : Measure E).real (A ∩ (s : Set E)) -
      (ν : Measure E).real (A ∩ (s : Set E))| ≤
      ∑ k ∈ s, |(μ : Measure E).real {k} - (ν : Measure E).real {k}|
```

### probability_event_le_finite_part_add_tail

lemma; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean:68)

```lean
private lemma probability_event_le_finite_part_add_tail (μ : ProbabilityMeasure E)
    (s : Finset E) (A : Set E) :
    (μ : Measure E).real A ≤ (μ : Measure E).real (A ∩ (s : Set E)) +
      (μ : Measure E).real (s : Set E)ᶜ
```

### probabilityTotalVariation_le_finite_sum

lemma; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean:80)

The finite-core estimate underlying the discrete Scheffé argument.

```lean
lemma probabilityTotalVariation_le_finite_sum (μ ν : ProbabilityMeasure E) (s : Finset E) :
    probabilityTotalVariation μ ν ≤
      2 * (∑ k ∈ s, |(μ : Measure E).real {k} - (ν : Measure E).real {k}|) +
      (ν : Measure E).real (s : Set E)ᶜ
```

### probability_finite_tail_tendsto

lemma; [source line 109](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean:109)

```lean
lemma probability_finite_tail_tendsto (ν : ProbabilityMeasure E) :
    Tendsto (fun s : Finset E => (ν : Measure E).real (s : Set E)ᶜ) atTop (𝓝 0)
```

### tendsto_probabilityTotalVariation_of_singletons

theorem; [source line 127](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountableTotalVariation.lean:127)

On a countable space, convergence of all point masses to a probability
law is uniform over all events. No tightness hypothesis is assumed.

```lean
theorem tendsto_probabilityTotalVariation_of_singletons
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (h : ∀ k, Tendsto (fun n => (μ n : Measure E).real {k}) atTop
      (𝓝 ((ν : Measure E).real {k}))) :
    Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0)
```


## Luce/Section4DiscreteTotalVariation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace Luce
```

### probabilityTotalVariation

def; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:19)

Probability total variation: the supremum over events, with no factor two.

```lean
def probabilityTotalVariation (μ ν : ProbabilityMeasure ℕ) : ℝ :=
  sSup (Set.range fun A : Set ℕ => |(μ : Measure ℕ).real A - (ν : Measure ℕ).real A|)
```

### probability_event_difference_le_one

lemma; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:22)

```lean
private lemma probability_event_difference_le_one (μ ν : ProbabilityMeasure ℕ)
    (A : Set ℕ) : |(μ : Measure ℕ).real A - (ν : Measure ℕ).real A| ≤ 1
```

### probabilityTotalVariation_nonneg

lemma; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:33)

```lean
lemma probabilityTotalVariation_nonneg (μ ν : ProbabilityMeasure ℕ) :
    0 ≤ probabilityTotalVariation μ ν
```

### probabilityTotalVariation_le_one

lemma; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:41)

```lean
lemma probabilityTotalVariation_le_one (μ ν : ProbabilityMeasure ℕ) :
    probabilityTotalVariation μ ν ≤ 1
```

### probability_event_difference_le_totalVariation

lemma; [source line 47](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:47)

```lean
lemma probability_event_difference_le_totalVariation (μ ν : ProbabilityMeasure ℕ)
    (A : Set ℕ) :
    |(μ : Measure ℕ).real A - (ν : Measure ℕ).real A| ≤ probabilityTotalVariation μ ν
```

### probability_finite_event_difference_le

lemma; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:53)

```lean
private lemma probability_finite_event_difference_le (μ ν : ProbabilityMeasure ℕ)
    (s : Finset ℕ) (A : Set ℕ) :
    |(μ : Measure ℕ).real (A ∩ (s : Set ℕ)) -
      (ν : Measure ℕ).real (A ∩ (s : Set ℕ))| ≤
      ∑ k ∈ s, |(μ : Measure ℕ).real {k} - (ν : Measure ℕ).real {k}|
```

### probability_event_le_finite_part_add_tail

lemma; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:66)

```lean
private lemma probability_event_le_finite_part_add_tail (μ : ProbabilityMeasure ℕ)
    (s : Finset ℕ) (A : Set ℕ) :
    (μ : Measure ℕ).real A ≤ (μ : Measure ℕ).real (A ∩ (s : Set ℕ)) +
      (μ : Measure ℕ).real (s : Set ℕ)ᶜ
```

### probabilityTotalVariation_le_finite_sum

lemma; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:78)

The finite-core estimate underlying the discrete Scheffé argument.

```lean
lemma probabilityTotalVariation_le_finite_sum (μ ν : ProbabilityMeasure ℕ) (s : Finset ℕ) :
    probabilityTotalVariation μ ν ≤
      2 * (∑ k ∈ s, |(μ : Measure ℕ).real {k} - (ν : Measure ℕ).real {k}|) +
      (ν : Measure ℕ).real (s : Set ℕ)ᶜ
```

### probability_nat_tail_tendsto

lemma; [source line 107](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:107)

```lean
private lemma probability_nat_tail_tendsto (ν : ProbabilityMeasure ℕ) :
    Tendsto (fun N : ℕ => (ν : Measure ℕ).real (Finset.Iic N : Set ℕ)ᶜ) atTop (𝓝 0)
```

### tendsto_probabilityTotalVariation_of_singletons

theorem; [source line 120](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:120)

Source: `fixed_points.tex:958–961`. Pointwise convergence of the masses to
a probability law implies convergence in probability total variation.

```lean
theorem tendsto_probabilityTotalVariation_of_singletons
    {μ : ℕ → ProbabilityMeasure ℕ} {ν : ProbabilityMeasure ℕ}
    (h : ∀ k, Tendsto (fun n => (μ n : Measure ℕ).real {k}) atTop
      (𝓝 ((ν : Measure ℕ).real {k}))) :
    Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0)
```

### tendsto_probability_singletons_of_weak

theorem; [source line 142](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:142)

Source: `fixed_points.tex:958–961`. Weak convergence on the discrete count
space implies the required singleton-probability convergence.

```lean
theorem tendsto_probability_singletons_of_weak
    {μ : ℕ → ProbabilityMeasure ℕ} {ν : ProbabilityMeasure ℕ}
    (h : Tendsto μ atTop (𝓝 ν)) (k : ℕ) :
    Tendsto (fun n => (μ n : Measure ℕ).real {k}) atTop
      (𝓝 ((ν : Measure ℕ).real {k}))
```

### tendsto_probabilityTotalVariation_of_weak

theorem; [source line 153](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:153)

Weak convergence to a proper natural-number law upgrades to total variation.

```lean
theorem tendsto_probabilityTotalVariation_of_weak
    {μ : ℕ → ProbabilityMeasure ℕ} {ν : ProbabilityMeasure ℕ}
    (h : Tendsto μ atTop (𝓝 ν)) :
    Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0)
```

### tendsto_probabilityTotalVariation_of_integrals

theorem; [source line 161](D:/princeton/Research/Lean/Lean_luce/Luce/Section4DiscreteTotalVariation.lean:161)

The same upgrade, directly in the bounded continuous test formulation of
weak convergence used for the point-process limit.

```lean
theorem tendsto_probabilityTotalVariation_of_integrals
    {μ : ℕ → ProbabilityMeasure ℕ} {ν : ProbabilityMeasure ℕ}
    (h : ∀ F : ℕ →ᵇ ℝ, Tendsto
      (fun n => ∫ k, F k ∂(μ n : Measure ℕ)) atTop
      (𝓝 (∫ k, F k ∂(ν : Measure ℕ)))) :
    Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0)
```


## Luce/Section2DrawHistory.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2DrawHistory.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
universe u
namespace Luce
```

### drawHistory

def; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section2DrawHistory.lean:19)

The sigma algebra generated by the first `m` draws, using the discrete
sigma algebra on the finite label set.

```lean
def drawHistory {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) : MeasurableSpace Ω :=
  ⨆ j : Fin n, ⨆ (_ : j.val < m),
    MeasurableSpace.comap (fun ω => π ω j) ⊤
```


## Luce/Section2DrawHistoryPermutation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2DrawHistoryPermutation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
namespace Luce
```

### inverse_ge_iff_no_earlier_draw

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section2DrawHistoryPermutation.lean:12)

A label remains before position `k` exactly when no earlier draw selected it.

```lean
theorem inverse_ge_iff_no_earlier_draw {n : ℕ} (π : Equiv.Perm (Fin n))
    (k i : Fin n) :
    k ≤ π.symm i ↔ ∀ j : Fin n, j < k → π j ≠ i
```


## Luce/Section3EmpiricalRace.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### arrivalAt

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:20)

```lean
def arrivalAt (t x : ℝ) : ℝ := if x ≤ t then 1 else 0
```

### arrivalAt_mem_Icc

lemma; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:22)

```lean
lemma arrivalAt_mem_Icc (t x : ℝ) : arrivalAt t x ∈ Icc (0 : ℝ) 1
```

### measurable_arrivalAt

lemma; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:26)

```lean
lemma measurable_arrivalAt (t : ℝ) : Measurable (arrivalAt t)
```

### arrivalAt_monotone

lemma; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:29)

```lean
lemma arrivalAt_monotone (x : ℝ) : Monotone (fun t => arrivalAt t x)
```

### integral_arrivalAt

lemma; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:34)

```lean
lemma integral_arrivalAt {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    (∫ x, arrivalAt t x ∂expMeasure r) = 1 - survivalKernel t r
```

### exponentialRace_integral_eval

lemma; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:44)

```lean
lemma exponentialRace_integral_eval {n : ℕ} (w : Weights n) (i : Fin n)
    (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ clocks, g (clocks i) ∂exponentialRace w) = ∫ x, g x ∂expMeasure (w.rate i)
```

### empiricalArrival

def; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:56)

```lean
def empiricalArrival {n : ℕ} (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, arrivalAt t (clocks i)) / n
```

### empiricalRemaining

def; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:59)

```lean
def empiricalRemaining {n : ℕ} (w : Weights n) (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, w.rate i * (1 - arrivalAt t (clocks i))) / n
```

### meanArrival

def; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:62)

```lean
def meanArrival {n : ℕ} (w : Weights n) (t : ℝ) : ℝ :=
  (∑ i, (1 - survivalKernel t (w.rate i))) / n
```

### meanRemaining

def; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:65)

```lean
def meanRemaining {n : ℕ} (w : Weights n) (t : ℝ) : ℝ :=
  (∑ i, rateKernel t (w.rate i)) / n
```

### memLp_empiricalArrival

lemma; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:68)

```lean
lemma memLp_empiricalArrival {n : ℕ} (w : Weights n) (t : ℝ) :
    MemLp (fun clocks => empiricalArrival clocks t) 2 (exponentialRace w)
```

### memLp_empiricalRemaining

lemma; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:78)

```lean
lemma memLp_empiricalRemaining {n : ℕ} (w : Weights n) (t : ℝ) :
    MemLp (fun clocks => empiricalRemaining w clocks t) 2 (exponentialRace w)
```

### integral_empiricalArrival

lemma; [source line 90](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:90)

```lean
lemma integral_empiricalArrival {n : ℕ} (w : Weights n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ clocks, empiricalArrival clocks t ∂exponentialRace w) = meanArrival w t
```

### integral_empiricalRemaining

lemma; [source line 106](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:106)

```lean
lemma integral_empiricalRemaining {n : ℕ} (w : Weights n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ clocks, empiricalRemaining w clocks t ∂exponentialRace w) = meanRemaining w t
```

### empiricalArrival_monotone

lemma; [source line 129](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:129)

```lean
lemma empiricalArrival_monotone {n : ℕ} (clocks : Fin n → ℝ) :
    Monotone (empiricalArrival clocks)
```

### empiricalRemaining_antitone

lemma; [source line 135](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:135)

```lean
lemma empiricalRemaining_antitone {n : ℕ} (w : Weights n) (clocks : Fin n → ℝ) :
    Antitone (empiricalRemaining w clocks)
```

### variance_empiricalArrival_le

lemma; [source line 145](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:145)

```lean
lemma variance_empiricalArrival_le {n : ℕ} (w : Weights (n + 1)) (t : ℝ) :
    variance (fun clocks => empiricalArrival clocks t) (exponentialRace w) ≤
      1 / (n + 1 : ℕ)
```

### variance_empiricalRemaining_le

lemma; [source line 170](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:170)

```lean
lemma variance_empiricalRemaining_le {n : ℕ} (w : Weights (n + 1)) (t : ℝ) {M : ℝ}
    (hnorm : ∑ i, w.rate i = (n + 1 : ℕ)) (hmax : ∀ i, w.rate i ≤ M) :
    variance (fun clocks => empiricalRemaining w clocks t) (exponentialRace w) ≤
      M / (n + 1 : ℕ)
```

### uniform_empiricalArrival

theorem; [source line 203](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:203)

The arrival half of the uniform race law, on the actual exponential
product measures.

```lean
theorem uniform_empiricalArrival {w : ∀ n, Weights (n + 1)} {F : ℝ → ℝ} {T : ℝ}
    (hF : ContinuousOn F (Icc 0 T))
    (hmean : ∀ t ∈ Icc 0 T, Tendsto (fun n => meanArrival (w n) t) atTop (𝓝 (F t))) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ t ∈ Icc 0 T, ε ≤ |empiricalArrival clocks t - F t|}) atTop (𝓝 0)
```

### uniform_empiricalRemaining

theorem; [source line 218](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:218)

The remaining-rate half of the uniform race law (strict survival).

```lean
theorem uniform_empiricalRemaining {w : ∀ n, Weights (n + 1)} {D : ℝ → ℝ} {T : ℝ}
    {M : ℕ → ℝ} (hD : ContinuousOn D (Icc 0 T))
    (hnorm : ∀ n, ∑ i, (w n).rate i = (n + 1 : ℕ))
    (hmax : ∀ n i, (w n).rate i ≤ M n)
    (hsmall : Tendsto (fun n => M n / (n + 1 : ℕ)) atTop (𝓝 0))
    (hmean : ∀ t ∈ Icc 0 T, Tendsto (fun n => meanRemaining (w n) t) atTop (𝓝 (D t))) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ t ∈ Icc 0 T, ε ≤ |empiricalRemaining (w n) clocks t - D t|})
      atTop (𝓝 0)
```

### empiricalRemainingGe

def; [source line 236](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:236)

The paper's weak-survival convention.

```lean
def empiricalRemainingGe {n : ℕ} (w : Weights n) (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, if t ≤ clocks i then w.rate i else 0) / n
```

### empiricalRemainingGe_antitone

lemma; [source line 239](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:239)

```lean
lemma empiricalRemainingGe_antitone {n : ℕ} (w : Weights n) (clocks : Fin n → ℝ) :
    Antitone (empiricalRemainingGe w clocks)
```

### empiricalRemainingGe_ae_eq

lemma; [source line 247](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:247)

```lean
lemma empiricalRemainingGe_ae_eq {n : ℕ} (w : Weights n) (t : ℝ) :
    (fun clocks => empiricalRemainingGe w clocks t) =ᵐ[exponentialRace w]
      (fun clocks => empiricalRemaining w clocks t)
```

### uniform_empiricalRemainingGe

theorem; [source line 271](D:/princeton/Research/Lean/Lean_luce/Luce/Section3EmpiricalRace.lean:271)

Uniform convergence for exactly the weak-survival process from
equation `eq:uniform-race`.

```lean
theorem uniform_empiricalRemainingGe {w : ∀ n, Weights (n + 1)} {D : ℝ → ℝ} {T : ℝ}
    {M : ℕ → ℝ} (hD : ContinuousOn D (Icc 0 T))
    (hnorm : ∀ n, ∑ i, (w n).rate i = (n + 1 : ℕ))
    (hmax : ∀ n i, (w n).rate i ≤ M n)
    (hsmall : Tendsto (fun n => M n / (n + 1 : ℕ)) atTop (𝓝 0))
    (hmean : ∀ t ∈ Icc 0 T, Tendsto (fun n => meanRemaining (w n) t) atTop (𝓝 (D t))) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ t ∈ Icc 0 T, ε ≤ |empiricalRemainingGe (w n) clocks t - D t|})
      atTop (𝓝 0)
```


## Luce/Section4EndpointEstimates.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
open Real Set MeasureTheory
namespace Luce
noncomputable section
```

### meanSurvivors

def; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean:24)

Expected number of survivors of independent exponential clocks.

```lean
def meanSurvivors {n : ℕ} (θ : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, Real.exp (-θ i * t)
```

### meanSurvivors_pos

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean:27)

```lean
theorem meanSurvivors_pos {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (t : ℝ) :
    0 < meanSurvivors θ t
```

### meanSurvivors_antitone

theorem; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean:34)

```lean
theorem meanSurvivors_antitone {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) : Antitone (meanSurvivors θ)
```

### half_rates_le_two

theorem; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean:42)

Mean-one normalization forces at least half the rates to be at most two.

```lean
theorem half_rates_le_two {n : ℕ} (θ : Fin n → ℝ) (hθ : ∀ i, 0 ≤ θ i)
    (hsum : ∑ i, θ i = (n : ℝ)) :
    (n : ℝ) / 2 ≤ ((Finset.univ.filter fun i => θ i ≤ 2).card : ℝ)
```

### meanSurvivors_lower_bound

theorem; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean:68)

The normalization bound `S(t) ≥ (n/2) exp(-2t)` from Section 4.

```lean
theorem meanSurvivors_lower_bound {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = (n : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    (n : ℝ) / 2 * Real.exp (-2 * t) ≤ meanSurvivors θ t
```

### exponential_density_le

theorem; [source line 89](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean:89)

At sufficiently late times all rates above `γ` have density at most
`γ exp(-γ t)`. This is the decreasing-density step of the endpoint proof.

```lean
theorem exponential_density_le {a γ t : ℝ} (hγ : 0 < γ) (ha : γ ≤ a)
    (ht : 1 ≤ γ * t) :
    a * Real.exp (-a * t) ≤ γ * Real.exp (-γ * t)
```

### integral_exponential_density_Ioi

theorem; [source line 108](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean:108)

Tail mass of an exponential density.

```lean
theorem integral_exponential_density_Ioi {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (∫ t : ℝ in Ioi s, a * Real.exp (-a * t)) = Real.exp (-a * s)
```

### integrableOn_exponential_density_Ioi

theorem; [source line 113](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean:113)

```lean
theorem integrableOn_exponential_density_Ioi {a : ℝ} (ha : 0 < a) (s : ℝ) :
    IntegrableOn (fun t : ℝ => a * Real.exp (-a * t)) (Ioi s)
```

### cutoff_exponential_le_rpow

theorem; [source line 119](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean:119)

Converting the mean-survivor cutoff into the power appearing in the
explicit endpoint estimate.

```lean
theorem cutoff_exponential_le_rpow {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = (n : ℝ))
    {s B γ : ℝ} (hs : 0 ≤ s) (hcut : meanSurvivors θ s = B) (hγ : 0 ≤ γ) :
    Real.exp (-γ * s) ≤ (2 * B / n) ^ (γ / 2)
```

### two_candidate_density_bound

theorem; [source line 139](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointEstimates.lean:139)

The deterministic two-candidate inequality, now with exponential
densities as weights.

```lean
theorem two_candidate_density_bound {α : Type*} [DecidableEq α]
    (survivors : Finset α) (candidate : ℕ → α) (M : ℕ) (θ : α → ℝ)
    {γ t : ℝ} (hγ : 0 < γ) (ht : 1 ≤ γ * t)
    (hθ : ∀ m ∈ Finset.Icc 1 M, γ ≤ θ (candidate m)) :
    (∑ m ∈ Finset.Icc 1 M,
      if (survivors.erase (candidate m)).card = m - 1
      then θ (candidate m) * Real.exp (-θ (candidate m) * t) else 0)
      ≤ 2 * γ * Real.exp (-γ * t)
```


## Luce/Section4EndpointAsymptotic.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators Topology
open Real Set MeasureTheory Filter
namespace Luce
noncomputable section
```

### terminalCandidate

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean:20)

The `m`th label counted back from the last label.

```lean
def terminalCandidate (n m : ℕ) : Fin (n + 1) :=
  ⟨n - (m - 1), Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
```

### terminalCandidate_val_add

lemma; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean:23)

```lean
lemma terminalCandidate_val_add {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n + 1) :
    (terminalCandidate n m).val + m = n + 1
```

### epsilonTailExpectation

def; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean:29)

Expected fixed points in the last `ceil (ε(n+1))` positions.

```lean
def epsilonTailExpectation (w : (n : ℕ) → Weights (n + 1)) (ε : ℝ) (n : ℕ) : ℝ :=
  ∫ clocks, (terminalFixedPointCount (terminalCandidate n) ⌈ε * (n + 1)⌉₊ clocks : ℝ)
    ∂exponentialRace (w n)
```

### epsilonTailExpectation_nonneg

lemma; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean:33)

```lean
lemma epsilonTailExpectation_nonneg (w : (n : ℕ) → Weights (n + 1)) (ε : ℝ) (n : ℕ) :
    0 ≤ epsilonTailExpectation w ε n
```

### tendsto_nat_add_one

lemma; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean:36)

```lean
lemma tendsto_nat_add_one : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop
```

### epsilonTailExpectation_eventually_le

theorem; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean:41)

The expectation bound is eventually valid with a linear cutoff whenever
`2 ε < β` and the cutoff stays beyond `1/γ`.

```lean
theorem epsilonTailExpectation_eventually_le
    (w : (n : ℕ) → Weights (n + 1))
    (hnorm : ∀ n, ∑ i, (w n).rate i = ((n + 1 : ℕ) : ℝ))
    {ε β γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (hgap : 2 * ε < β)
    (hβone : β ≤ 1) (hβsmall : β ≤ Real.exp (-2 / γ) / 2)
    (hrate : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε * (n + 1)⌉₊,
      γ ≤ (w n).rate (terminalCandidate n m)) :
    ∀ᶠ n in atTop, epsilonTailExpectation w ε n ≤
      (ε * (n + 1) + 1) * Real.exp (-(bernoulliLowerTailConstant / 2) * (β * (n + 1))) +
        2 * (2 * β) ^ (γ / 2)
```

### tendsto_endpoint_early_envelope

lemma; [source line 98](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean:98)

The rounded linear prefactor is dominated by exponential decay.

```lean
lemma tendsto_endpoint_early_envelope {ε β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n : ℕ => (ε * (n + 1) + 1) *
      Real.exp (-(bernoulliLowerTailConstant / 2) * (β * (n + 1)))) atTop (𝓝 0)
```

### epsilonTailExpectation_limsup_le

theorem; [source line 119](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean:119)

The endpoint limsup bound for any admissible linear cutoff fraction.

```lean
theorem epsilonTailExpectation_limsup_le
    (w : (n : ℕ) → Weights (n + 1))
    (hnorm : ∀ n, ∑ i, (w n).rate i = ((n + 1 : ℕ) : ℝ))
    {ε β γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (hgap : 2 * ε < β)
    (hβone : β ≤ 1) (hβsmall : β ≤ Real.exp (-2 / γ) / 2)
    (hrate : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε * (n + 1)⌉₊,
      γ ≤ (w n).rate (terminalCandidate n m)) :
    limsup (epsilonTailExpectation w ε) atTop ≤ 2 * (2 * β) ^ (γ / 2)
```

### epsilonTailExpectation_power_limsup

theorem; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean:141)

The exact power and constant in equation `eq:tail-epsilon`.

```lean
theorem epsilonTailExpectation_power_limsup
    (w : (n : ℕ) → Weights (n + 1))
    (hnorm : ∀ n, ∑ i, (w n).rate i = ((n + 1 : ℕ) : ℝ))
    {ε γ : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 4) (hγ : 0 < γ)
    (hcutoff : Real.sqrt ε ≤ Real.exp (-2 / γ) / 2)
    (hrate : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε * (n + 1)⌉₊,
      γ ≤ (w n).rate (terminalCandidate n m)) :
    limsup (epsilonTailExpectation w ε) atTop ≤
      (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4)
```

### endpoint_epsilon_estimate

theorem; [source line 167](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointAsymptotic.lean:167)

A uniform rate lower bound on one fixed terminal neighborhood implies
the paper's epsilon estimate for every sufficiently small positive epsilon.

```lean
theorem endpoint_epsilon_estimate
    (w : (n : ℕ) → Weights (n + 1))
    (hnorm : ∀ n, ∑ i, (w n).rate i = ((n + 1 : ℕ) : ℝ))
    {γ ε₀ : ℝ} (hγ : 0 < γ) (hε₀ : 0 < ε₀)
    (hrate : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε₀ * (n + 1)⌉₊,
      γ ≤ (w n).rate (terminalCandidate n m)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      limsup (epsilonTailExpectation w ε) atTop ≤
        (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4)
```


## Luce/Section4EndpointBlockCapacity.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointBlockCapacity.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Luce
```

### capacity_candidate_density_le

theorem; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointBlockCapacity.lean:13)

```lean
theorem capacity_candidate_density_le {n : ℕ} (w : Weights n) (i : Fin n)
    (q : ℕ) {t : ℝ} (ht : 0 < t) :
    w.rate i * Real.exp (-w.rate i * t) * otherSurvivorProbability w i q t ≤
      (w.rate i / (Real.exp (w.rate i * t) - 1)) * fullSurvivorProbability w q t
```

### capacity_block_density_le

theorem; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointBlockCapacity.lean:34)

```lean
theorem capacity_block_density_le {n : ℕ} (w : Weights (n + 1))
    (block : Finset (Fin (n + 1))) {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hrate : ∀ i ∈ block, a ≤ w.rate i) :
    (∑ i ∈ block, w.rate i * Real.exp (-w.rate i * t) *
      otherSurvivorProbability w i (n - i.val) t) ≤ a / (Real.exp (a * t) - 1)
```

### capacity_other_survivor_early

theorem; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointBlockCapacity.lean:55)

```lean
theorem capacity_other_survivor_early {n : ℕ} (w : Weights n) (i : Fin n)
    {q : ℕ} {r s t : ℝ} (hr : 0 ≤ r) (hq : (q : ℝ) ≤ r)
    (hcut : r < meanSurvivors w.rate s - 1) (ht : 0 ≤ t) (hts : t ≤ s) :
    otherSurvivorProbability w i q t ≤
      Real.exp (-((meanSurvivors w.rate s - 1 - r) ^ 2 /
        (2 * (meanSurvivors w.rate s - 1))))
```

### exponentialRace_block_capacity

theorem; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointBlockCapacity.lean:78)

`eq:block-endpoint-capacity`, with arbitrary lower/upper bounds on the
block rates and depths. Taking the finite minimum and maximum gives exactly
the manuscript statement. No asymptotic assumption is used.

```lean
theorem exponentialRace_block_capacity {n : ℕ} (w : Weights (n + 1))
    (block : Finset (Fin (n + 1))) {a r s : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hs : 0 < s)
    (hrate : ∀ i ∈ block, a ≤ w.rate i)
    (hdepth : ∀ i ∈ block, ((n - i.val : ℕ) : ℝ) ≤ r)
    (hcut : r < meanSurvivors w.rate s - 1) :
    (∑ i ∈ block, (exponentialRace w).real {e | raceRank e i = i.val + 1}) ≤
      (block.card : ℝ) * Real.exp (-((meanSurvivors w.rate s - 1 - r) ^ 2 /
        (2 * (meanSurvivors w.rate s - 1)))) + endpointQ (a * s)
```


## Luce/Section4EndpointBlockExpectation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointBlockExpectation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Real Set
open scoped BigOperators
namespace Luce
```

### block_fixedPoint_expectation_eq

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointBlockExpectation.lean:12)

The sum of fixed-point probabilities in a block is its actual expected
number of fixed labels. No integrability input is necessary for a finite count.

```lean
theorem block_fixedPoint_expectation_eq {n : ℕ} (w : Weights n) (block : Finset (Fin n)) :
    (∫ e, ((block.filter fun i => raceRank e i = i.val + 1).card : ℝ) ∂exponentialRace w) =
      ∑ i ∈ block, (exponentialRace w).real {e | raceRank e i = i.val + 1}
```

### block_endpoint_capacity

theorem; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointBlockExpectation.lean:37)

Literal finite minimum and maximum specialization of block capacity.
The extra local quantities in `exponentialRace_block_capacity` are constructed
here, rather than assumed of the weight array.

```lean
theorem block_endpoint_capacity {n : ℕ} (w : Weights (n + 1))
    (block : Finset (Fin (n + 1))) (hb : block.Nonempty) (s : ℝ) (hs : 0 < s)
    (hcut : (((block.image terminalDepth).max' (hb.image _)) : ℝ) <
      meanSurvivors w.rate s - 1) :
    (∫ e, ((block.filter fun i => raceRank e i = i.val + 1).card : ℝ) ∂exponentialRace w) ≤
      (block.card : ℝ) * Real.exp (-((meanSurvivors w.rate s - 1 -
        (((block.image terminalDepth).max' (hb.image _)) : ℝ)) ^ 2 /
          (2 * (meanSurvivors w.rate s - 1)))) +
        endpointQ (((block.image w.rate).min' (hb.image _)) * s)
```


## Luce/Section4EndpointBlockIntegral.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointBlockIntegral.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Real Set
open scoped BigOperators
namespace Luce
```

### capacity_integral_bound

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointBlockIntegral.lean:11)

```lean
theorem capacity_integral_bound {ι : Type*} (indices : Finset ι)
    (θ : ι → ℝ) (p : ι → ℝ → ℝ) {γ s q : ℝ}
    (hγ : 0 < γ) (hs : 0 < s) (hq : 0 ≤ q)
    (hθ : ∀ i ∈ indices, γ ≤ θ i)
    (hpmeas : ∀ i ∈ indices, Measurable (p i))
    (hp : ∀ t ∈ Ioi 0, ∀ i ∈ indices, 0 ≤ p i t ∧ p i t ≤ 1)
    (hearly : ∀ t ∈ Ioc 0 s, ∀ i ∈ indices, p i t ≤ q)
    (hlate : ∀ t ∈ Ioi s, (∑ i ∈ indices, θ i * Real.exp (-θ i * t) * p i t) ≤ γ / (Real.exp (γ * t) - 1)) :
    (∑ i ∈ indices, ∫ t : ℝ in Ioi 0, θ i * Real.exp (-θ i * t) * p i t) ≤
      (indices.card : ℝ) * q + endpointQ (γ * s)
```


## Luce/Section4EndpointCapacityAnalytic.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
namespace Luce
```

### endpointQ

def; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:13)

```lean
def endpointQ (x : ℝ) : ℝ := -Real.log (1 - Real.exp (-x))
```

### endpointQ_pos

theorem; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:15)

```lean
theorem endpointQ_pos {x : ℝ} (hx : 0 < x) : 0 < endpointQ x
```

### endpointQ_antitone

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:21)

```lean
theorem endpointQ_antitone : AntitoneOn endpointQ (Ioi 0)
```

### exp_neg_le_endpointQ

theorem; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:29)

```lean
theorem exp_neg_le_endpointQ {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ endpointQ x
```

### endpointQ_le_two_exp

theorem; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:36)

```lean
theorem endpointQ_le_two_exp {x : ℝ} (hx : Real.exp (-x) ≤ 1 / 2) :
    endpointQ x ≤ 2 * Real.exp (-x)
```

### hasDerivAt_log_one_sub_exp

theorem; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:48)

```lean
theorem hasDerivAt_log_one_sub_exp {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.log (1 - Real.exp (-a * s)))
      (a / (Real.exp (a * t) - 1)) t
```

### tendsto_log_one_sub_exp

theorem; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:65)

```lean
theorem tendsto_log_one_sub_exp (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => Real.log (1 - Real.exp (-a * t))) atTop (𝓝 0)
```

### integral_capacity_kernel

theorem; [source line 75](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:75)

Exact late-time kernel integral in the manuscript's block bound.

```lean
theorem integral_capacity_kernel {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    (∫ t in Ioi s, a / (Real.exp (a * t) - 1)) = endpointQ (a * s)
```

### integrable_capacity_kernel

theorem; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:84)

```lean
theorem integrable_capacity_kernel {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    IntegrableOn (fun t => a / (Real.exp (a * t) - 1)) (Ioi s)
```

### capacity_kernel_antitone

theorem; [source line 94](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:94)

Monotonicity in the rate, valid at every positive time. This has no
late-time threshold of the form `a*t ≥ 1`.

```lean
theorem capacity_kernel_antitone {t : ℝ} (ht : 0 < t) :
    AntitoneOn (fun a : ℝ => a / (Real.exp (a * t) - 1)) (Ioi 0)
```

### exp_neg_le_quadratic

theorem; [source line 117](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityAnalytic.lean:117)

The quadratic exponential estimate needed for the exact Chernoff
exponent in the manuscript's block proposition.

```lean
theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2
```


## Luce/Section4EndpointCapacityChernoff.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityChernoff.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace Luce
```

### bernoulli_block_lower_tail

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityChernoff.lean:11)

Exact lower-tail exponent with a lower bound B on the true mean.
All premises are discharged by survivor means in the intended application.

```lean
theorem bernoulli_block_lower_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι)
    {r B : ℝ} (hr : 0 ≤ r) (hrB : r < B)
    (hB : B ≤ ∑ i ∈ indices, ∫ ω, X i ω ∂μ) :
    μ.real {ω | (∑ i ∈ indices, X i ω) ≤ r} ≤
      Real.exp (-((B - r) ^ 2 / (2 * B)))
```


## Luce/Section4EndpointCapacityProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Luce
```

### fullSurvivorProbability

def; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityProbability.lean:9)

```lean
def fullSurvivorProbability {n : ℕ} (w : Weights n) (q : ℕ) (t : ℝ) : ℝ :=
  (exponentialRace w).real {e | (∑ i, clockSurvivalIndicator t i e) = (q : ℝ)}
```

### removed_survivor_probability_le

theorem; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityProbability.lean:14)

Removing a candidate costs its probability of already having rung.
Independence is proved from the canonical exponential product measure.

```lean
theorem removed_survivor_probability_le {n : ℕ} (w : Weights n) (i : Fin n)
    (q : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 - Real.exp (-w.rate i * t)) * otherSurvivorProbability w i q t ≤
      fullSurvivorProbability w q t
```

### sum_fullSurvivorProbability_le_one

theorem; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCapacityProbability.lean:62)

```lean
theorem sum_fullSurvivorProbability_le_one {n : ℕ} (w : Weights (n + 1))
    (s : Finset (Fin (n + 1))) (t : ℝ) :
    ∑ i ∈ s, fullSurvivorProbability w (n - i.val) t ≤ 1
```


## Luce/Section4EndpointCutoff.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCutoff.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators Topology
open Real Set Filter
namespace Luce
```

### continuous_meanSurvivors

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCutoff.lean:11)

```lean
theorem continuous_meanSurvivors {n : ℕ} (θ : Fin n → ℝ) :
    Continuous (meanSurvivors θ)
```

### meanSurvivors_zero

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCutoff.lean:17)

```lean
theorem meanSurvivors_zero {n : ℕ} (θ : Fin n → ℝ) : meanSurvivors θ 0 = n
```

### meanSurvivors_strictAnti

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCutoff.lean:20)

```lean
theorem meanSurvivors_strictAnti {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) : StrictAnti (meanSurvivors θ)
```

### tendsto_meanSurvivors_atTop

theorem; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCutoff.lean:29)

```lean
theorem tendsto_meanSurvivors_atTop {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) : Tendsto (meanSurvivors θ) atTop (𝓝 0)
```

### exists_unique_meanSurvivors_cutoff

theorem; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCutoff.lean:40)

The cutoff used by the paper exists and is unique whenever `0 < B ≤ n`.

```lean
theorem exists_unique_meanSurvivors_cutoff {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) {B : ℝ} (hB : 0 < B) (hBn : B ≤ n) :
    ∃! s : ℝ, 0 ≤ s ∧ meanSurvivors θ s = B
```

### meanSurvivors_cutoff_log_lower

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointCutoff.lean:56)

The lower bound on the cutoff stated in the proof of the endpoint bound.

```lean
theorem meanSurvivors_cutoff_log_lower {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = (n : ℝ))
    {s B : ℝ} (hs : 0 ≤ s) (hcut : meanSurvivors θ s = B) :
    (1 / 2 : ℝ) * Real.log ((n : ℝ) / (2 * B)) ≤ s
```


## Luce/Section4EndpointIntegrals.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointIntegrals.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
open Real Set MeasureTheory
namespace Luce
noncomputable section
```

### probability_weighted_density_bound

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointIntegrals.lean:19)

A sum of candidate densities is bounded by twice the slowest admissible
density when the sum of the candidate probabilities is at most two.

```lean
theorem probability_weighted_density_bound {ι : Type*} (indices : Finset ι)
    (θ p : ι → ℝ) {γ t : ℝ} (hγ : 0 < γ) (ht : 1 ≤ γ * t)
    (hθ : ∀ i ∈ indices, γ ≤ θ i) (hp : ∀ i ∈ indices, 0 ≤ p i)
    (hsum : ∑ i ∈ indices, p i ≤ 2) :
    (∑ i ∈ indices, θ i * Real.exp (-θ i * t) * p i) ≤
      2 * γ * Real.exp (-γ * t)
```

### probability_weighted_tail_bound

theorem; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointIntegrals.lean:37)

Integrating the two-candidate envelope gives the exact terminal term
`2 exp(-γ s)` in the paper.

```lean
theorem probability_weighted_tail_bound {ι : Type*} (indices : Finset ι)
    (θ : ι → ℝ) (p : ι → ℝ → ℝ) {γ s : ℝ} (hγ : 0 < γ)
    (hs : 1 ≤ γ * s) (hθ : ∀ i ∈ indices, γ ≤ θ i)
    (hpmeas : ∀ i ∈ indices, Measurable (p i))
    (hp : ∀ t ∈ Ioi s, ∀ i ∈ indices, 0 ≤ p i t)
    (hsum : ∀ t ∈ Ioi s, ∑ i ∈ indices, p i t ≤ 2) :
    (∫ t : ℝ in Ioi s, ∑ i ∈ indices, θ i * Real.exp (-θ i * t) * p i t)
      ≤ 2 * Real.exp (-γ * s)
```

### integrableOn_probability_weighted_density

theorem; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointIntegrals.lean:76)

Integrability of a probability-weighted exponential density.

```lean
theorem integrableOn_probability_weighted_density {a s : ℝ} (ha : 0 < a)
    (p : ℝ → ℝ) (hmeas : Measurable p)
    (hp : ∀ t ∈ Ioi s, 0 ≤ p t ∧ p t ≤ 1) :
    IntegrableOn (fun t => a * Real.exp (-a * t) * p t) (Ioi s)
```

### endpoint_integral_bound

theorem; [source line 90](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointIntegrals.lean:90)

Splitting the candidate rank integrals at the survivor cutoff gives the
two terms in the explicit endpoint bound.

```lean
theorem endpoint_integral_bound {ι : Type*} (indices : Finset ι)
    (θ : ι → ℝ) (p : ι → ℝ → ℝ) {γ s q : ℝ}
    (hγ : 0 < γ) (hs : 1 ≤ γ * s) (hq : 0 ≤ q)
    (hθ : ∀ i ∈ indices, γ ≤ θ i)
    (hpmeas : ∀ i ∈ indices, Measurable (p i))
    (hp : ∀ t ∈ Ioi 0, ∀ i ∈ indices, 0 ≤ p i t ∧ p i t ≤ 1)
    (hearly : ∀ t ∈ Ioc 0 s, ∀ i ∈ indices, p i t ≤ q)
    (hlate : ∀ t ∈ Ioi s, ∑ i ∈ indices, p i t ≤ 2) :
    (∑ i ∈ indices, ∫ t : ℝ in Ioi 0, θ i * Real.exp (-θ i * t) * p i t) ≤
      (indices.card : ℝ) * q + 2 * Real.exp (-γ * s)
```


## Luce/Section4EndpointJensen.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointJensen.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
namespace Luce
```

### meanSurvivors_jensen

theorem; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointJensen.lean:10)

Jensen's bound with coefficient one in logarithmic time. The proof uses
the supporting line `exp x ≥ 1+x`; it requires no bound on individual rates.

```lean
theorem meanSurvivors_jensen {n : ℕ} (θ : Fin n → ℝ)
    (hsum : ∑ i, θ i = (n : ℝ)) (t : ℝ) :
    (n : ℝ) * Real.exp (-t) ≤ meanSurvivors θ t
```

### NormalizedWeights.meanSurvivors_jensen

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointJensen.lean:27)

```lean
theorem NormalizedWeights.meanSurvivors_jensen {w : WeightArray}
    (hnorm : NormalizedWeights w) (n : ℕ) (t : ℝ) :
    (n : ℝ) * Real.exp (-t) ≤ meanSurvivors (w n).rate t
```


## Luce/Section4EndpointProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
open Real Set MeasureTheory ProbabilityTheory
namespace Luce
noncomputable section
```

### two_candidate_probability_bound

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointProbability.lean:20)

The sum of the probabilities of all terminal candidate events is at
most two, for any random survivor set.

```lean
theorem two_candidate_probability_bound {Ω α : Type*} [MeasurableSpace Ω]
    [DecidableEq α] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (survivors : Ω → Finset α) (candidate : ℕ → α) (M : ℕ)
    (hmeas : ∀ m ∈ Finset.Icc 1 M,
      MeasurableSet {ω | ((survivors ω).erase (candidate m)).card = m - 1}) :
    (∑ m ∈ Finset.Icc 1 M,
      μ.real {ω | ((survivors ω).erase (candidate m)).card = m - 1}) ≤ 2
```

### bernoulliLowerTailConstant

def; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointProbability.lean:55)

The universal positive constant in the Bernoulli lower-tail estimate.

```lean
def bernoulliLowerTailConstant : ℝ := 1 / 2 - Real.exp (-1)
```

### bernoulliLowerTailConstant_pos

theorem; [source line 57](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointProbability.lean:57)

```lean
theorem bernoulliLowerTailConstant_pos : 0 < bernoulliLowerTailConstant
```

### integrable_of_zero_one

theorem; [source line 67](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointProbability.lean:67)

A zero-one random variable is integrable on a probability space.

```lean
theorem integrable_of_zero_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) : Integrable X μ
```

### mgf_neg_one_of_zero_one

theorem; [source line 75](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointProbability.lean:75)

The Laplace transform of a Bernoulli variable at parameter one.

```lean
theorem mgf_neg_one_of_zero_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) :
    mgf X μ (-1) = 1 - (1 - Real.exp (-1)) * ∫ ω, X ω ∂μ
```

### bernoulli_sum_lower_tail

theorem; [source line 89](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointProbability.lean:89)

The multiplicative Chernoff lower-tail estimate for a finite sum of
independent Bernoulli variables. No identical-distribution hypothesis is used.

```lean
theorem bernoulli_sum_lower_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι) :
    μ.real {ω | (∑ i ∈ indices, X i ω) ≤ (∑ i ∈ indices, ∫ ω, X i ω ∂μ) / 2} ≤
      Real.exp (-bernoulliLowerTailConstant * (∑ i ∈ indices, ∫ ω, X i ω ∂μ))
```

### bernoulli_sum_eq_le_cutoff

theorem; [source line 139](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointProbability.lean:139)

A version of the lower-tail bound with the mean replaced by the paper's
cutoff `B`. The hypotheses are exactly the numerical inequalities established
for the other-survivor count before time `s`.

```lean
theorem bernoulli_sum_eq_le_cutoff {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι) {m B : ℝ}
    (hm : m ≤ (∑ i ∈ indices, ∫ ω, X i ω ∂μ) / 2)
    (hB : B / 2 ≤ ∑ i ∈ indices, ∫ ω, X i ω ∂μ) :
    μ.real {ω | (∑ i ∈ indices, X i ω) = m} ≤
      Real.exp (-(bernoulliLowerTailConstant / 2) * B)
```


## Luce/Section4EndpointRace.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
open Real Set MeasureTheory ProbabilityTheory
namespace Luce
noncomputable section
```

### clockSurvivalIndicator

def; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:18)

```lean
def clockSurvivalIndicator {n : ℕ} (t : ℝ) (i : Fin n) (clocks : Fin n → ℝ) : ℝ :=
  if t < clocks i then 1 else 0
```

### measurable_clockSurvivalIndicator

lemma; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:21)

```lean
lemma measurable_clockSurvivalIndicator {n : ℕ} (t : ℝ) (i : Fin n) :
    Measurable (clockSurvivalIndicator t i)
```

### clockSurvivalIndicator_zero_one

lemma; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:26)

```lean
lemma clockSurvivalIndicator_zero_one {n : ℕ} (t : ℝ) (i : Fin n)
    (clocks : Fin n → ℝ) :
    clockSurvivalIndicator t i clocks = 0 ∨ clockSurvivalIndicator t i clocks = 1
```

### integral_clockSurvivalIndicator

lemma; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:32)

```lean
lemma integral_clockSurvivalIndicator {n : ℕ} (w : Weights n) (t : ℝ)
    (ht : 0 ≤ t) (i : Fin n) :
    (∫ clocks, clockSurvivalIndicator t i clocks ∂exponentialRace w) =
      Real.exp (-w.rate i * t)
```

### clockSurvivalIndicator_independent

lemma; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:45)

```lean
lemma clockSurvivalIndicator_independent {n : ℕ} (w : Weights n) (t : ℝ) :
    iIndepFun (clockSurvivalIndicator t) (exponentialRace w)
```

### other_survivors_eq_sum

lemma; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:52)

```lean
lemma other_survivors_eq_sum {n : ℕ} (clocks : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    (((survivorSet clocks t).erase i).card : ℝ) =
      ∑ j ∈ Finset.univ.erase i, clockSurvivalIndicator t j clocks
```

### measurable_other_survivors

lemma; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:62)

```lean
lemma measurable_other_survivors {n : ℕ} (i : Fin n) :
    Measurable (fun z : ℝ × (Fin n → ℝ) => ((survivorSet z.2 z.1).erase i).card)
```

### otherSurvivorProbability

def; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:72)

Probability that exactly `m` other clocks survive at time `t`.

```lean
def otherSurvivorProbability {n : ℕ} (w : Weights n) (i : Fin n) (m : ℕ) (t : ℝ) : ℝ :=
  (exponentialRace w).real {clocks | ((survivorSet clocks t).erase i).card = m}
```

### measurable_otherSurvivorProbability

lemma; [source line 75](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:75)

```lean
lemma measurable_otherSurvivorProbability {n : ℕ} (w : Weights n) (i : Fin n) (m : ℕ) :
    Measurable (otherSurvivorProbability w i m)
```

### otherSurvivorProbability_nonneg

lemma; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:80)

```lean
lemma otherSurvivorProbability_nonneg {n : ℕ} (w : Weights n) (i : Fin n) (m : ℕ) (t : ℝ) :
    0 ≤ otherSurvivorProbability w i m t
```

### otherSurvivorProbability_le_one

lemma; [source line 83](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:83)

```lean
lemma otherSurvivorProbability_le_one {n : ℕ} (w : Weights n) (i : Fin n) (m : ℕ) (t : ℝ) :
    otherSurvivorProbability w i m t ≤ 1
```

### sum_otherSurvivorProbability_le_two

lemma; [source line 87](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:87)

```lean
lemma sum_otherSurvivorProbability_le_two {n : ℕ} (w : Weights n)
    (candidate : ℕ → Fin n) (M : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.Icc 1 M, otherSurvivorProbability w (candidate m) (m - 1) t) ≤ 2
```

### mean_other_survivors_lower

lemma; [source line 96](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:96)

The expected other-survivor count differs from `S(t)` by at most one.

```lean
lemma mean_other_survivors_lower {n : ℕ} (w : Weights n) (i : Fin n)
    {t : ℝ} (ht : 0 ≤ t) :
    meanSurvivors w.rate t - 1 ≤
      ∑ j ∈ Finset.univ.erase i,
        ∫ clocks, clockSurvivalIndicator t j clocks ∂exponentialRace w
```

### otherSurvivorProbability_early

theorem; [source line 112](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:112)

Uniform early-time bound for every terminal candidate.

```lean
theorem otherSurvivorProbability_early {n : ℕ} (w : Weights n) (i : Fin n)
    {m M : ℕ} {t s B : ℝ} (_hm : 1 ≤ m) (hmM : m ≤ M) (hM : 1 ≤ M)
    (ht : 0 ≤ t) (hts : t ≤ s) (hcut : meanSurvivors w.rate s = B)
    (hBM : 2 * (M : ℝ) ≤ B - 1) :
    otherSurvivorProbability w i (m - 1) t ≤
      Real.exp (-(bernoulliLowerTailConstant / 2) * B)
```

### exponentialRace_endpoint_integrals

theorem; [source line 139](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:139)

The endpoint estimate with the candidate probabilities and exponential
clock law fully instantiated. The rank-integral identity converts the left
side into the expected number of terminal fixed points.

```lean
theorem exponentialRace_endpoint_integrals {n : ℕ} (w : Weights n)
    (candidate : ℕ → Fin n) {M : ℕ} {s B γ : ℝ}
    (hM : 1 ≤ M) (hγ : 0 < γ)
    (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (candidate m))
    (hcut : meanSurvivors w.rate s = B) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hs : 1 ≤ γ * s) :
    (∑ m ∈ Finset.Icc 1 M, ∫ t : ℝ in Ioi 0,
      w.rate (candidate m) * Real.exp (-w.rate (candidate m) * t) *
        otherSurvivorProbability w (candidate m) (m - 1) t) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) * B) +
        2 * Real.exp (-γ * s)
```

### exponentialRace_endpoint_integrals_power

theorem; [source line 163](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointRace.lean:163)

Normalization gives the second, power-law form of the finite endpoint
bound.

```lean
theorem exponentialRace_endpoint_integrals_power {n : ℕ} (hn : 0 < n) (w : Weights n)
    (hnorm : ∑ i, w.rate i = (n : ℝ)) (candidate : ℕ → Fin n)
    {M : ℕ} {s B γ : ℝ} (hM : 1 ≤ M) (hγ : 0 < γ)
    (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (candidate m))
    (hcut : meanSurvivors w.rate s = B) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hs : 1 ≤ γ * s) :
    (∑ m ∈ Finset.Icc 1 M, ∫ t : ℝ in Ioi 0,
      w.rate (candidate m) * Real.exp (-w.rate (candidate m) * t) *
        otherSurvivorProbability w (candidate m) (m - 1) t) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) * B) +
        2 * (2 * B / n) ^ (γ / 2)
```


## Luce/Section4EndpointShellBuffer.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBuffer.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Real Set Filter
open scoped Topology BigOperators ENNReal
namespace Luce
```

### buffer_exp_bound

theorem; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBuffer.lean:13)

Pointwise splitting inequality, with `s = sqrt j`.

```lean
theorem buffer_exp_bound (b s : ℝ) (hs : 1 ≤ s) :
    Real.exp (-b * (s ^ 2 - s)) ≤
      Real.exp 1 * Real.exp (-b * s ^ 2) + Real.exp (1 - s)
```

### summable_buffer_error

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBuffer.lean:27)

The error sequence is genuinely summable, not an assumed envelope.

```lean
theorem summable_buffer_error : Summable (fun j : ℕ => Real.exp (1 - Real.sqrt j))
```

### bufferedShellExpCost

def; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBuffer.lean:52)

Exponential buffered costs are used only for j≥2, where the cutoff
is positive. Dropping finitely many indices has no effect on the tail limit.

```lean
def bufferedShellExpCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  if hj : 2 ≤ j then
    if h : (terminalShell n j).Nonempty then
      ENNReal.ofReal (Real.exp (-shellFloor w n j h * ((j : ℝ) - Real.sqrt j))) else 0
  else 0
```

### bufferedShellQCost

def; [source line 58](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBuffer.lean:58)

```lean
def bufferedShellQCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  if hj : 2 ≤ j then
    if h : (terminalShell n j).Nonempty then
      ENNReal.ofReal (endpointQ (shellFloor w n j h * ((j : ℝ) - Real.sqrt j))) else 0
  else 0
```

### bufferedShellExpCost_le

theorem; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBuffer.lean:64)

```lean
theorem bufferedShellExpCost_le (w : WeightArray) (n j : ℕ) :
    bufferedShellExpCost w n j ≤ ENNReal.ofReal (Real.exp 1) * shellCost w n j +
      ENNReal.ofReal (Real.exp (1 - Real.sqrt j))
```


## Luce/Section4EndpointShellBufferLimit.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBufferLimit.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Filter Set
open scoped Topology BigOperators ENNReal
namespace Luce
```

### nonnegativeTail

def; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBufferLimit.lean:8)

```lean
def nonnegativeTail (p : ℕ → ℕ → ℝ≥0∞) (n J : ℕ) : ℝ≥0∞ :=
  ∑' j : ℕ, if J ≤ j then p n j else 0
```

### nonnegativeTail_antitone

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBufferLimit.lean:11)

```lean
theorem nonnegativeTail_antitone (p : ℕ → ℕ → ℝ≥0∞) (n : ℕ) :
    Antitone (nonnegativeTail p n)
```

### nonnegativeTail_limit_iff

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBufferLimit.lean:19)

Generic equivalence used only as an internal limit lemma.

```lean
theorem nonnegativeTail_limit_iff (p : ℕ → ℕ → ℝ≥0∞) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail p n J) atTop) atTop (𝓝 0) ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ J : ℕ,
        ∀ᶠ n : ℕ in atTop, nonnegativeTail p n J < ε
```

### buffered_exp_tail_bound

theorem; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBufferLimit.lean:35)

```lean
theorem buffered_exp_tail_bound (w : WeightArray) (n J : ℕ) :
    nonnegativeTail (bufferedShellExpCost w) n J ≤
      ENNReal.ofReal (Real.exp 1) * shellTailCost w n J +
        ∑' j : ℕ, if J ≤ j then ENNReal.ofReal (Real.exp (1 - Real.sqrt j)) else 0
```

### EndpointShellAssumption.buffered_exp

theorem; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBufferLimit.lean:46)

```lean
theorem EndpointShellAssumption.buffered_exp {w : WeightArray}
    (h : EndpointShellAssumption w) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (bufferedShellExpCost w) n J) atTop)
      atTop (𝓝 0)
```

### bufferedShellQCost_le_of_small_tail

theorem; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBufferLimit.lean:69)

```lean
theorem bufferedShellQCost_le_of_small_tail (w : WeightArray) (n J : ℕ)
    (hsmall : nonnegativeTail (bufferedShellExpCost w) n J ≤ ENNReal.ofReal (1 / 2)) :
    nonnegativeTail (bufferedShellQCost w) n J ≤
      2 * nonnegativeTail (bufferedShellExpCost w) n J
```

### EndpointShellAssumption.buffered_Q

theorem; [source line 98](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBufferLimit.lean:98)

The actual diagonal shell-buffer conclusion, derived from the raw
assumption alone. The cutoff 2 only avoids undefined nonpositive Q arguments.

```lean
theorem EndpointShellAssumption.buffered_Q {w : WeightArray}
    (h : EndpointShellAssumption w) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (bufferedShellQCost w) n J) atTop)
      atTop (𝓝 0)
```

### EndpointShellAssumption.buffered_Q_raw

theorem; [source line 120](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellBufferLimit.lean:120)

Removing the harmless finite cutoff gives the literal manuscript buffer
sum. Empty shells remain excluded, and the order of limits is unchanged.

```lean
theorem EndpointShellAssumption.buffered_Q_raw {w : WeightArray}
    (h : EndpointShellAssumption w) :
    Tendsto (fun J : ℕ => limsup (fun n : ℕ => ∑' j : ℕ,
      if J ≤ j then
        if hs : (terminalShell n j).Nonempty then
          ENNReal.ofReal (endpointQ (shellFloor w n j hs * ((j : ℝ) - Real.sqrt j)))
        else 0
      else 0) atTop) atTop (𝓝 0)
```


## Luce/Section4EndpointShellCompatibility.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellCompatibility.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Filter Set
open scoped BigOperators Topology ENNReal
namespace Luce
```

### ennreal_tendsto_tail_sum

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellCompatibility.lean:9)

```lean
theorem ennreal_tendsto_tail_sum {a : ℕ → ℝ≥0∞} (ha : ∑' j, a j ≠ ⊤) :
    Tendsto (fun J : ℕ => ∑' j : ℕ, if J ≤ j then a j else 0) atTop (𝓝 0)
```

### shell_label_terminal

theorem; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellCompatibility.lean:22)

Membership in a deep logarithmic shell places the label in the
specified terminal fraction. No condition on the weights is used.

```lean
theorem shell_label_terminal {n j : ℕ} {k : Fin n} (hk : k ∈ terminalShell n j)
    {ε : ℝ} (hε : 0 < ε) (hj : -Real.log ε ≤ (j : ℝ)) :
    (1 - ε) * (n : ℝ) ≤ (k.val : ℝ) + 1
```

### UniformEndpointAssumption.shell

theorem; [source line 47](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellCompatibility.lean:47)

Compatibility with the old theorem: uniform terminal positivity implies
the exact shell condition. Normalization and profile convergence are not needed.

```lean
theorem UniformEndpointAssumption.shell {w : WeightArray}
    (h : UniformEndpointAssumption w) : EndpointShellAssumption w
```


## Luce/Section4EndpointShellCover.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellCover.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open scoped BigOperators
namespace Luce
```

### terminalShell_cover

theorem; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellCover.lean:8)

```lean
theorem terminalShell_cover {n J : ℕ} (hJ : 1 ≤ J) (k : Fin n)
    (hk : (J : ℝ) ≤ Real.log ((n : ℝ)/(terminalDepth k : ℝ))) :
    ∃ j ∈ Finset.range (n+1), J ≤ j ∧ k ∈ terminalShell n j
```

### spatial_tail_log_lower

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellCover.lean:17)

```lean
theorem spatial_tail_log_lower {n J : ℕ} (k : Fin n)
    (hn : 2 ≤ (n : ℝ)*Real.exp (-(J : ℝ)))
    (hk : (1-Real.exp (-(J : ℝ))/2)*(n : ℝ) < (k.val : ℝ)+1) :
    (J : ℝ) ≤ Real.log ((n : ℝ)/(terminalDepth k : ℝ))
```


## Luce/Section4EndpointShellDefinitions.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellDefinitions.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace Luce
```

### UniformEndpointAssumption

abbrev; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellDefinitions.lean:17)

Historical uniform condition, retained without changing its meaning.

```lean
abbrev UniformEndpointAssumption := EndpointAssumption
```

### terminalDepth

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellDefinitions.lean:20)

Depth one is the last label; `k.val + 1` is its manuscript label.

```lean
def terminalDepth {n : ℕ} (k : Fin n) : ℕ := n - k.val
```

### terminalShell

def; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellDefinitions.lean:23)

Shell represented by its labels. The explicit `1 ≤ j` excludes shell zero.

```lean
def terminalShell (n j : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k => 1 ≤ j ∧
    (j : ℝ) ≤ Real.log ((n : ℝ) / (terminalDepth k : ℝ)) ∧
    Real.log ((n : ℝ) / (terminalDepth k : ℝ)) < (j : ℝ) + 1
```

### shellFloor

def; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellDefinitions.lean:30)

The finite minimum exists only when the shell is nonempty.

```lean
def shellFloor (w : WeightArray) (n j : ℕ) (h : (terminalShell n j).Nonempty) : ℝ :=
  ((terminalShell n j).image (w n).rate).min' (h.image _)
```

### shellCost

def; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellDefinitions.lean:34)

Empty shells contribute zero, not `exp 0`.

```lean
def shellCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  if h : (terminalShell n j).Nonempty then
    ENNReal.ofReal (Real.exp (-shellFloor w n j h * (j : ℝ))) else 0
```

### shellTailCost

def; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellDefinitions.lean:40)

The literal sum over all nonempty shells of index at least `J`.
Finite support is proved separately, not presumed in the definition.

```lean
def shellTailCost (w : WeightArray) (n J : ℕ) : ℝ≥0∞ :=
  ∑' j : ℕ, if J ≤ j then shellCost w n j else 0
```

### EndpointShellAssumption

def; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellDefinitions.lean:45)

The manuscript's iterated limit, with no uniform-in-row strengthening.
Normalization is deliberately separate. Row zero is empty and irrelevant.

```lean
def EndpointShellAssumption (w : WeightArray) : Prop :=
  Tendsto (fun J : ℕ => limsup (fun n : ℕ => shellTailCost w n J) atTop)
    atTop (𝓝 (0 : ℝ≥0∞))
```


## Luce/Section4EndpointShellEarly.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellEarly.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
namespace Luce
```

### capacity_exponent_lower

theorem; [source line 7](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellEarly.lean:7)

```lean
theorem capacity_exponent_lower {r A B : ℝ} (hr : 1 ≤ r) (hA : 4 ≤ A)
    (hB : r * A - 1 ≤ B) : r * A / 16 ≤ (B - r)^2 / (2 * B)
```

### shell_early_envelope

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellEarly.lean:19)

A summable envelope in the shell index itself avoids any extra
summability assumption or a count of shell maxima.

```lean
theorem shell_early_envelope {r h B : ℝ} (hr : 1 ≤ r) (hh : 64 ≤ h)
    (hB : r * Real.exp h - 1 ≤ B) :
    r * Real.exp (-((B-r)^2 / (2*B))) ≤ Real.exp (1-h)
```


## Luce/Section4EndpointShellEstimate.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellEstimate.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace Luce
```

### shell_survivor_buffer

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellEstimate.lean:11)

```lean
theorem shell_survivor_buffer {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j : ℕ) (hs : (terminalShell n j).Nonempty) :
    (shellMax n j hs : ℝ) * Real.exp (Real.sqrt j) ≤
      meanSurvivors (w n).rate ((j : ℝ) - Real.sqrt j)
```

### shell_block_expectation_le

theorem; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellEstimate.lean:25)

```lean
theorem shell_block_expectation_le {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j : ℕ) (hj : 4096 ≤ j) (hb : (terminalShell (n+1) j).Nonempty) :
    (∫ e, (((terminalShell (n+1) j).filter fun i => raceRank e i = i.val+1).card : ℝ)
      ∂exponentialRace (w (n+1))) ≤
      Real.exp (1-Real.sqrt j) +
      endpointQ (shellFloor w (n+1) j hb * ((j : ℝ)-Real.sqrt j))
```


## Luce/Section4EndpointShellExpectationLimit.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellExpectationLimit.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Luce
```

### shellExpectationCost

def; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellExpectationLimit.lean:9)

```lean
def shellExpectationCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ i ∈ terminalShell n j,
    (exponentialRace (w n)).real {e | raceRank e i = i.val+1})
```

### shellExpectationCost_le

theorem; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellExpectationLimit.lean:13)

```lean
theorem shellExpectationCost_le {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j : ℕ) (hj : 4096 ≤ j) :
    shellExpectationCost w n j ≤ ENNReal.ofReal (Real.exp (1-Real.sqrt j)) +
      bufferedShellQCost w n j
```

### shellExpectationTail_bound

theorem; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellExpectationLimit.lean:34)

```lean
theorem shellExpectationTail_bound {w : WeightArray} (hnorm : NormalizedWeights w)
    (n J : ℕ) (hJ : 4096 ≤ J) :
    nonnegativeTail (shellExpectationCost w) n J ≤
      (∑' j : ℕ, if J ≤ j then ENNReal.ofReal (Real.exp (1-Real.sqrt j)) else 0) +
      nonnegativeTail (bufferedShellQCost w) n J
```

### EndpointShellAssumption.expectation_shells

theorem; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellExpectationLimit.lean:48)

Shell expectation tightness is derived from normalization and the raw
shell condition, without any profile or uniform endpoint bound.

```lean
theorem EndpointShellAssumption.expectation_shells {w : WeightArray}
    (h : EndpointShellAssumption w) (hnorm : NormalizedWeights w) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (shellExpectationCost w) n J) atTop)
      atTop (𝓝 0)
```


## Luce/Section4EndpointShellGeometry.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellGeometry.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open scoped BigOperators
namespace Luce
```

### shellMax

def; [source line 7](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellGeometry.lean:7)

```lean
def shellMax (n j : ℕ) (h : (terminalShell n j).Nonempty) : ℕ :=
  ((terminalShell n j).image terminalDepth).max' (h.image _)
```

### shellMax_attained

theorem; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellGeometry.lean:10)

```lean
theorem shellMax_attained (n j : ℕ) (h : (terminalShell n j).Nonempty) :
    ∃ k ∈ terminalShell n j, terminalDepth k = shellMax n j h
```

### shellMax_pos

theorem; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellGeometry.lean:15)

```lean
theorem shellMax_pos (n j : ℕ) (h : (terminalShell n j).Nonempty) :
    0 < shellMax n j h
```

### shellMax_log

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellGeometry.lean:21)

```lean
theorem shellMax_log (n j : ℕ) (h : (terminalShell n j).Nonempty) :
    (j : ℝ) ≤ Real.log ((n : ℝ) / shellMax n j h)
```

### shell_card_le_max

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellGeometry.lean:27)

```lean
theorem shell_card_le_max (n j : ℕ) (h : (terminalShell n j).Nonempty) :
    (terminalShell n j).card ≤ shellMax n j h
```

### shellMax_exp_le

theorem; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellGeometry.lean:40)

```lean
theorem shellMax_exp_le (n j : ℕ) (h : (terminalShell n j).Nonempty) :
    (shellMax n j h : ℝ) * Real.exp (j : ℝ) ≤ n
```


## Luce/Section4EndpointShells.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Filter Set
open scoped BigOperators Topology ENNReal
namespace Luce
```

### terminalDepth_pos

theorem; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:10)

```lean
theorem terminalDepth_pos {n : ℕ} (k : Fin n) : 0 < terminalDepth k
```

### terminalDepth_le

theorem; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:14)

```lean
theorem terminalDepth_le {n : ℕ} (k : Fin n) : terminalDepth k ≤ n
```

### terminalDepth_add_label

theorem; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:16)

```lean
theorem terminalDepth_add_label {n : ℕ} (k : Fin n) :
    terminalDepth k + (k.val + 1) = n + 1
```

### terminalDepth_labelOfDepth

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:21)

```lean
theorem terminalDepth_labelOfDepth {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    terminalDepth (⟨n - m, by omega⟩ : Fin n) = m
```

### terminalDepth_injective

theorem; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:26)

```lean
theorem terminalDepth_injective (n : ℕ) :
    Function.Injective (terminalDepth : Fin n → ℕ)
```

### mem_terminalShell

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:33)

```lean
theorem mem_terminalShell {n j : ℕ} {k : Fin n} :
    k ∈ terminalShell n j ↔ 1 ≤ j ∧
      (j : ℝ) ≤ Real.log ((n : ℝ) / (terminalDepth k : ℝ)) ∧
      Real.log ((n : ℝ) / (terminalDepth k : ℝ)) < (j : ℝ) + 1
```

### shellFloor_attained

theorem; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:40)

```lean
theorem shellFloor_attained (w : WeightArray) (n j : ℕ)
    (h : (terminalShell n j).Nonempty) :
    ∃ k ∈ terminalShell n j, shellFloor w n j h = (w n).rate k
```

### shellFloor_pos

theorem; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:48)

```lean
theorem shellFloor_pos (w : WeightArray) (n j : ℕ)
    (h : (terminalShell n j).Nonempty) : 0 < shellFloor w n j h
```

### shellFloor_le_rate

theorem; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:54)

```lean
theorem shellFloor_le_rate (w : WeightArray) {n j : ℕ}
    (h : (terminalShell n j).Nonempty) {k : Fin n} (hk : k ∈ terminalShell n j) :
    shellFloor w n j h ≤ (w n).rate k
```

### le_shellFloor

theorem; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:60)

```lean
theorem le_shellFloor (w : WeightArray) {n j : ℕ}
    (h : (terminalShell n j).Nonempty) {a : ℝ}
    (ha : ∀ k ∈ terminalShell n j, a ≤ (w n).rate k) :
    a ≤ shellFloor w n j h
```

### shell_index_le_row

theorem; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:69)

A coarse finite bound suffices: no nonempty shell has index greater than n.

```lean
theorem shell_index_le_row {n j : ℕ} (h : (terminalShell n j).Nonempty) : j ≤ n
```

### shellCost_eq_zero_of_row_lt

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:81)

```lean
theorem shellCost_eq_zero_of_row_lt (w : WeightArray) {n j : ℕ} (h : n < j) :
    shellCost w n j = 0
```

### shellCost_le_one

theorem; [source line 86](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:86)

```lean
theorem shellCost_le_one (w : WeightArray) (n j : ℕ) : shellCost w n j ≤ 1
```

### shellTailCost_eq_sum

theorem; [source line 95](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:95)

This identifies the raw infinite sum with an actual finite row sum.

```lean
theorem shellTailCost_eq_sum (w : WeightArray) (n J : ℕ) :
    shellTailCost w n J = ∑ j ∈ Finset.range (n + 1),
      if J ≤ j then shellCost w n j else 0
```

### shellTailCost_ne_top

theorem; [source line 103](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:103)

```lean
theorem shellTailCost_ne_top (w : WeightArray) (n J : ℕ) : shellTailCost w n J ≠ ⊤
```

### shellTailCost_antitone

theorem; [source line 112](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:112)

```lean
theorem shellTailCost_antitone (w : WeightArray) (n : ℕ) : Antitone (shellTailCost w n)
```

### endpointShellAssumption_iff_eventually

theorem; [source line 120](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShells.lean:120)

Equivalence, not just a sufficient strengthening. The row threshold is
chosen after the tail cutoff and the requested error.

```lean
theorem endpointShellAssumption_iff_eventually (w : WeightArray) :
    EndpointShellAssumption w ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ J : ℕ,
        ∀ᶠ n : ℕ in atTop, shellTailCost w n J < ε
```


## Luce/Section4EndpointShellTailBridge.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellTailBridge.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Luce
```

### sum_spatial_tail_le_shells

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellTailBridge.lean:9)

```lean
theorem sum_spatial_tail_le_shells {n J : ℕ} (hJ : 1 ≤ J)
    (hn : 2 ≤ (n : ℝ)*Real.exp (-(J : ℝ))) (p : Fin n → ℝ≥0∞) :
    (∑ i ∈ Finset.univ.filter (fun k : Fin n =>
      (1-Real.exp (-(J : ℝ))/2)*(n : ℝ) < (k.val : ℝ)+1), p i) ≤
      ∑ j ∈ Finset.range (n+1), if J ≤ j then ∑ i ∈ terminalShell n j, p i else 0
```

### spatial_tail_expectation_le_shells

theorem; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellTailBridge.lean:37)

```lean
theorem spatial_tail_expectation_le_shells (w : WeightArray) (n J : ℕ) (hJ : 1 ≤ J)
    (hn : 2 ≤ (n : ℝ)*Real.exp (-(J : ℝ))) :
    ENNReal.ofReal (∫ e, (tailFixedPointCount e (1-Real.exp (-(J : ℝ))/2) : ℝ)
      ∂exponentialRace (w n)) ≤ nonnegativeTail (shellExpectationCost w) n J
```


## Luce/Section4EndpointShellTightness.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellTightness.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Luce
```

### EndpointShellAssumption.expectation_tightness

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellTightness.lean:11)

The actual spatial endpoint expectation estimate. All cutoff and
eventual-row choices are conclusions derived from the raw shell condition.

```lean
theorem EndpointShellAssumption.expectation_tightness {w : WeightArray}
    (h : EndpointShellAssumption w) (hnorm : NormalizedWeights w) :
    ∀ η : ℝ, 0 < η → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ᶠ n : ℕ in atTop,
        (∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace (w n)) < η
```

### tailFixedPointCount_antitone

theorem; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellTightness.lean:34)

```lean
theorem tailFixedPointCount_antitone {n : ℕ} (e : Fin n → ℝ) :
    Antitone (tailFixedPointCount e)
```

### tailExpectation_antitone

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellTightness.lean:43)

```lean
theorem tailExpectation_antitone (w : WeightArray) (n : ℕ) :
    Antitone (fun α : ℝ => ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace (w n))
```

### EndpointShellAssumption.probability_tightness

theorem; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointShellTightness.lean:53)

Probability tightness follows from the proved expectation estimate.

```lean
theorem EndpointShellAssumption.probability_tightness {w : WeightArray}
    (h : EndpointShellAssumption w) (hnorm : NormalizedWeights w) :
    Tendsto (fun α : ℝ => limsup (fun n : ℕ =>
      (exponentialRace (w n)).real {e | 0 < tailFixedPointCount e α}) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```


## Luce/Section4EndpointTheorem.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointTheorem.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
open Real Set MeasureTheory
namespace Luce
noncomputable section
```

### measurable_raceRank

lemma; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointTheorem.lean:20)

```lean
lemma measurable_raceRank {n : ℕ} (i : Fin n) :
    Measurable (fun clocks : Fin n → ℝ => raceRank clocks i)
```

### terminalFixedPointCount

def; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointTheorem.lean:32)

Count of fixed points among the selected terminal labels.

```lean
def terminalFixedPointCount {n : ℕ} (candidate : ℕ → Fin n) (M : ℕ)
    (clocks : Fin n → ℝ) : ℕ :=
  ((Finset.Icc 1 M).filter fun m => raceRank clocks (candidate m) = (candidate m).val + 1).card
```

### integral_terminalFixedPointCount

lemma; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointTheorem.lean:36)

```lean
lemma integral_terminalFixedPointCount {n : ℕ} (w : Weights n)
    (candidate : ℕ → Fin n) (M : ℕ) :
    (∫ clocks, (terminalFixedPointCount candidate M clocks : ℝ) ∂exponentialRace w) =
      ∑ m ∈ Finset.Icc 1 M,
        (exponentialRace w).real {clocks | raceRank clocks (candidate m) = (candidate m).val + 1}
```

### endpoint_fixedPoint_probability_bound

theorem; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointTheorem.lean:65)

The first explicit inequality in Proposition `prop:endpoint-bound`.
All probabilities, independence and rank conditioning are discharged in the
finite exponential-clock model. The positive universal Chernoff constant is
`(1/2 - exp(-1))/2`.

```lean
theorem endpoint_fixedPoint_probability_bound {n : ℕ} (w : Weights (n + 1))
    (candidate : ℕ → Fin (n + 1)) {M : ℕ} {s B γ : ℝ}
    (hM : 1 ≤ M) (hterminal : ∀ m ∈ Finset.Icc 1 M, (candidate m).val + m = n + 1)
    (hγ : 0 < γ) (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (candidate m))
    (hcut : meanSurvivors w.rate s = B) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hs : 1 ≤ γ * s) :
    (∑ m ∈ Finset.Icc 1 M,
      (exponentialRace w).real {clocks | raceRank clocks (candidate m) = (candidate m).val + 1}) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) * B) +
        2 * Real.exp (-γ * s)
```

### endpoint_fixedPoint_expectation_bound

theorem; [source line 90](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointTheorem.lean:90)

Proposition `prop:endpoint-bound`, in expectation form.

```lean
theorem endpoint_fixedPoint_expectation_bound {n : ℕ} (w : Weights (n + 1))
    (candidate : ℕ → Fin (n + 1)) {M : ℕ} {s B γ : ℝ}
    (hM : 1 ≤ M) (hterminal : ∀ m ∈ Finset.Icc 1 M, (candidate m).val + m = n + 1)
    (hγ : 0 < γ) (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (candidate m))
    (hcut : meanSurvivors w.rate s = B) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hs : 1 ≤ γ * s) :
    (∫ clocks, (terminalFixedPointCount candidate M clocks : ℝ) ∂exponentialRace w) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) * B) +
        2 * Real.exp (-γ * s)
```

### endpoint_fixedPoint_expectation_power_bound

theorem; [source line 104](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointTheorem.lean:104)

The normalized power bound in the second inequality of
`eq:tail-explicit`. Taking `B = sqrt ((n+1) * M)` gives the paper's expression.

```lean
theorem endpoint_fixedPoint_expectation_power_bound {n : ℕ} (w : Weights (n + 1))
    (hnorm : ∑ i, w.rate i = ((n + 1 : ℕ) : ℝ))
    (candidate : ℕ → Fin (n + 1)) {M : ℕ} {s B γ : ℝ}
    (hM : 1 ≤ M) (hterminal : ∀ m ∈ Finset.Icc 1 M, (candidate m).val + m = n + 1)
    (hγ : 0 < γ) (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (candidate m))
    (hcut : meanSurvivors w.rate s = B) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hs : 1 ≤ γ * s) :
    (∫ clocks, (terminalFixedPointCount candidate M clocks : ℝ) ∂exponentialRace w) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) * B) +
        2 * (2 * B / (n + 1)) ^ (γ / 2)
```


## Luce/Section4ExponentialFacts.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialFacts.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Set
namespace Luce
```

### instance at line 10

instance; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialFacts.lean:10)

```lean
instance expMeasure_nullSingleton (r : ℝ) : NullSingletonClass (expMeasure r) := by
  change NullSingletonClass (volume.withDensity (exponentialPDF r))
  infer_instance
```

### expMeasure_Ici

lemma; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialFacts.lean:14)

```lean
lemma expMeasure_Ici {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    expMeasure r (Ici t) = ENNReal.ofReal (Real.exp (-(r * t)))
```

### exponentialRace_survival_ge

lemma; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialFacts.lean:19)

```lean
lemma exponentialRace_survival_ge {n : ℕ} (w : Weights n) (i : Fin n)
    (t : ℝ) (ht : 0 ≤ t) :
    exponentialRace w {clocks | t ≤ clocks i} =
      ENNReal.ofReal (Real.exp (-(w.rate i * t)))
```

### exponentialRace_collision_zero

lemma; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialFacts.lean:28)

```lean
lemma exponentialRace_collision_zero {n : ℕ} (w : Weights n) {i j : Fin n} (hij : i ≠ j) :
    exponentialRace w {clocks | clocks i = clocks j} = 0
```

### exponentialRace_injective_ae

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialFacts.lean:43)

Independent exponential clocks are pairwise distinct almost surely.

```lean
theorem exponentialRace_injective_ae {n : ℕ} (w : Weights n) :
    ∀ᵐ clocks ∂exponentialRace w, Function.Injective clocks
```


## Luce/Section3ExponentialMemoryless.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ExponentialMemoryless.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Set
namespace Luce
```

### exponential_residual_measure

theorem; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ExponentialMemoryless.lean:15)

After survival to a deterministic time `s`, subtracting `s` from an
exponential clock leaves the original exponential law, multiplied by the
survival probability. This unnormalized identity avoids conditioning on a
zero-probability exact clock value.

```lean
theorem exponential_residual_measure {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    ((expMeasure r).restrict (Ioi s)).map (fun x => x - s) =
      ENNReal.ofReal (Real.exp (-(r * s))) • expMeasure r
```


## Luce/Section4ExponentialRace.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set
namespace Luce
```

### exponentialRace

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:22)

Joint law of the independent exponential clocks.

```lean
noncomputable def exponentialRace {n : ℕ} (w : Weights n) : Measure (Fin n → ℝ) :=
  Measure.pi fun i => expMeasure (w.rate i)
```

### instance at line 25

instance; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:25)

```lean
instance exponentialRace_isProbability {n : ℕ} (w : Weights n) :
    IsProbabilityMeasure (exponentialRace w) := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  unfold exponentialRace
  infer_instance
```

### expMeasure_Ioi

lemma; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:33)

The one-dimensional exponential survival function.

```lean
lemma expMeasure_Ioi {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    expMeasure r (Set.Ioi t) = ENNReal.ofReal (Real.exp (-(r * t)))
```

### exponentialRace_eval

lemma; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:43)

Evaluation of one coordinate has the prescribed exponential law.

```lean
lemma exponentialRace_eval {n : ℕ} (w : Weights n) (i : Fin n) :
    MeasurePreserving (Function.eval i) (exponentialRace w) (expMeasure (w.rate i))
```

### exponentialRace_independent

lemma; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:50)

The coordinate clocks are mutually independent.

```lean
lemma exponentialRace_independent {n : ℕ} (w : Weights n) :
    iIndepFun (fun i (clocks : Fin n → ℝ) => clocks i) (exponentialRace w)
```

### exponentialRace_survival

lemma; [source line 57](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:57)

Exact survival probability of a coordinate.

```lean
lemma exponentialRace_survival {n : ℕ} (w : Weights n) (i : Fin n)
    (t : ℝ) (ht : 0 ≤ t) :
    exponentialRace w {clocks | t < clocks i} =
      ENNReal.ofReal (Real.exp (-(w.rate i * t)))
```

### backgroundRace

def; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:66)

The `n` other clocks, indexed by deleting the distinguished label.

```lean
noncomputable def backgroundRace {n : ℕ} (w : Weights (n + 1)) (i : Fin (n + 1)) :
    Measure (Fin n → ℝ) :=
  Measure.pi fun j => expMeasure (w.rate (i.succAbove j))
```

### instance at line 70

instance; [source line 70](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:70)

```lean
instance backgroundRace_isProbability {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) : IsProbabilityMeasure (backgroundRace w i) := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (w.rate (i.succAbove j))) :=
    fun j => isProbabilityMeasure_expMeasure (w.positive _)
  unfold backgroundRace
  infer_instance
```

### backgroundSurvivors

def; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:78)

Number of background clocks surviving at time `t`.

```lean
noncomputable def backgroundSurvivors {n : ℕ} (t : ℝ) (clocks : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun j => t < clocks j).card
```

### measurable_backgroundSurvivors

lemma; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:81)

```lean
lemma measurable_backgroundSurvivors {n : ℕ} :
    Measurable (fun z : ℝ × (Fin n → ℝ) => backgroundSurvivors z.1 z.2)
```

### exponentialRace_disintegrate

theorem; [source line 93](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:93)

The exact conditioning identity for any nonnegative measurable statistic
of one distinguished clock and its background.

```lean
theorem exponentialRace_disintegrate {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (g : ℝ × (Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ clocks, g (clocks i, fun j => clocks (i.succAbove j)) ∂exponentialRace w) =
      ∫⁻ t, exponentialPDF (w.rate i) t *
        (∫⁻ background, g (t, background) ∂backgroundRace w i)
```

### rank_integral_survivors

theorem; [source line 113](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ExponentialRace.lean:113)

Equation `eq:rank-integral`, expressed as a nonnegative Lebesgue integral.
The event says exactly `m` other clocks ring after the candidate. For distinct
clocks this is rank `n + 1 - m`, by `raceRank_eq_iff_survivors`.

```lean
theorem rank_integral_survivors {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (m : ℕ) :
    exponentialRace w {clocks |
      backgroundSurvivors (clocks i) (fun j => clocks (i.succAbove j)) = m} =
      ∫⁻ t, exponentialPDF (w.rate i) t *
        backgroundRace w i {background | backgroundSurvivors t background = m}
```


## Luce/Section2FiniteAdaptedBernoulli.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
namespace Luce
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
namespace FiniteAdaptedBernoulli
variable {P : Measure Ω} {n : ℕ} (B : FiniteAdaptedBernoulli P n)
variable [IsProbabilityMeasure P]
```

### FiniteAdaptedBernoulli

structure; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:22)

A finite adapted zero-one row. The filtration index is shifted by one
because `Fin n` starts at zero: observation `k` is available at time `k+1`.

```lean
structure FiniteAdaptedBernoulli (P : Measure Ω) (n : ℕ) where
  filtration : Filtration ℕ mΩ
  observation : Fin n → Ω → Bool
  adapted : ∀ k, Measurable[filtration (k.val + 1)] (observation k)
```

### observationReal

def; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:32)

The real-valued zero-one observation represented by the Boolean datum.

```lean
def observationReal (k : Fin n) (ω : Ω) : ℝ :=
  if B.observation k ω then 1 else 0
```

### observationReal_zero_one

theorem; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:35)

```lean
theorem observationReal_zero_one (k : Fin n) (ω : Ω) :
    B.observationReal k ω = 0 ∨ B.observationReal k ω = 1
```

### observationReal_nonneg

theorem; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:40)

```lean
theorem observationReal_nonneg (k : Fin n) (ω : Ω) :
    0 ≤ B.observationReal k ω
```

### observationReal_le_one

theorem; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:44)

```lean
theorem observationReal_le_one (k : Fin n) (ω : Ω) :
    B.observationReal k ω ≤ 1
```

### observationReal_adapted

theorem; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:48)

```lean
theorem observationReal_adapted (k : Fin n) :
    StronglyMeasurable[B.filtration (k.val + 1)] (B.observationReal k)
```

### probability

def; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:56)

A canonical everywhere-bounded version of the predictable conditional
probability. It agrees almost everywhere with the conditional expectation.

```lean
noncomputable def probability (k : Fin n) (ω : Ω) : ℝ :=
  max 0 (min 1 (P[B.observationReal k | B.filtration k.val] ω))
```

### probability_nonneg

theorem; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:59)

```lean
theorem probability_nonneg (k : Fin n) (ω : Ω) :
    0 ≤ B.probability k ω
```

### probability_le_one

theorem; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:62)

```lean
theorem probability_le_one (k : Fin n) (ω : Ω) :
    B.probability k ω ≤ 1
```

### probability_predictable

theorem; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:65)

```lean
theorem probability_predictable (k : Fin n) :
    StronglyMeasurable[B.filtration k.val] (B.probability k)
```

### integrable_observationReal

theorem; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:72)

```lean
theorem integrable_observationReal (k : Fin n) : Integrable (B.observationReal k) P
```

### integrable_probability

theorem; [source line 77](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:77)

```lean
theorem integrable_probability (k : Fin n) : Integrable (B.probability k) P
```

### conditional_mean

theorem; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:84)

Clipping changes only a null exceptional set, since a conditional
expectation of a zero-one observation lies in `[0,1]` almost everywhere.

```lean
theorem conditional_mean (k : Fin n) :
    P[B.observationReal k | B.filtration k.val] =ᵐ[P] B.probability k
```

### probability_ae_eq_condExp

theorem; [source line 94](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:94)

```lean
theorem probability_ae_eq_condExp (k : Fin n) :
    B.probability k =ᵐ[P] P[B.observationReal k | B.filtration k.val]
```

### toProcess

def; [source line 101](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:101)

Extend the finite row by zero observations and zero probabilities.
All analytic fields of `BernoulliProcess` follow from adaptation and the
conditional expectation; none is additional row data.

```lean
noncomputable def toProcess : BernoulliProcess P where
  filtration := B.filtration
  observation k := if hk : k < n then B.observationReal ⟨k, hk⟩ else 0
  probability k := if hk : k < n then B.probability ⟨k, hk⟩ else 0
  adapted k := by
    split_ifs with hk
    · exact B.observationReal_adapted ⟨k, hk⟩
    · exact stronglyMeasurable_zero
  predictable k := by
    split_ifs with hk
    · exact B.probability_predictable ⟨k, hk⟩
    · exact stronglyMeasurable_zero
  zero_one k ω := by
    split_ifs with hk
    · exact B.observationReal_zero_one ⟨k, hk⟩ ω
    · exact Or.inl rfl
  probability_nonneg k ω := by
    split_ifs with hk
    · exact B.probability_nonneg ⟨k, hk⟩ ω
    · exact le_rfl
  probability_le_one k ω := by
    split_ifs with hk
    · exact B.probability_le_one ⟨k, hk⟩ ω
    · norm_num
  conditional_mean k := by
    split_ifs with hk
    · exact B.conditional_mean ⟨k, hk⟩
    · rw [condExp_zero]
```

### toProcess_filtration

theorem; [source line 130](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:130)

```lean
@[simp] theorem toProcess_filtration : B.toProcess.filtration = B.filtration
```

### toProcess_observation

theorem; [source line 132](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:132)

```lean
@[simp] theorem toProcess_observation (k : Fin n) :
    B.toProcess.observation k.val = B.observationReal k
```

### toProcess_probability

theorem; [source line 136](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:136)

```lean
@[simp] theorem toProcess_probability (k : Fin n) :
    B.toProcess.probability k.val = B.probability k
```

### toProcess_observation_of_le

theorem; [source line 140](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:140)

```lean
theorem toProcess_observation_of_le {k : ℕ} (hk : n ≤ k) :
    B.toProcess.observation k = 0
```

### toProcess_probability_of_le

theorem; [source line 144](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteAdaptedBernoulli.lean:144)

```lean
theorem toProcess_probability_of_le {k : ℕ} (hk : n ≤ k) :
    B.toProcess.probability k = 0
```


## Luce/Section2FiniteBernoulliRow.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
open scoped BigOperators
namespace Luce.BernoulliProcess
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable [IsProbabilityMeasure μ]
```

### rowMaximum

def; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:13)

Maximum of the individual probabilities in a finite row, with empty
maximum zero. Coincident spatial locations do not combine coefficients.

```lean
noncomputable def rowMaximum (Y : BernoulliProcess μ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | N + 1, ω => max (rowMaximum Y N ω) (Y.probability N ω)
```

### rowMaximum_nonneg

lemma; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:17)

```lean
lemma rowMaximum_nonneg (N : ℕ) (ω : Ω) : 0 ≤ X.rowMaximum N ω
```

### measurable_rowMaximum

lemma; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:22)

```lean
lemma measurable_rowMaximum (N : ℕ) : Measurable (X.rowMaximum N)
```

### probability_le_rowMaximum

lemma; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:28)

```lean
lemma probability_le_rowMaximum {N k : ℕ} (hk : k < N) (ω : Ω) :
    X.probability k ω ≤ X.rowMaximum N ω
```

### truncateAt

def; [source line 39](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:39)

Zero extension of a finite row. No hypothesis on the original process
after `N` is needed, and its filtration is retained exactly.

```lean
noncomputable def truncateAt (N : ℕ) : BernoulliProcess μ where
  filtration := X.filtration
  observation k := if k < N then X.observation k else fun _ => 0
  probability k := if k < N then X.probability k else fun _ => 0
  adapted k := by
    split_ifs
    · exact X.adapted k
    · exact stronglyMeasurable_zero
  predictable k := by
    split_ifs
    · exact X.predictable k
    · exact stronglyMeasurable_zero
  zero_one k ω := by
    split_ifs
    · exact X.zero_one k ω
    · exact Or.inl rfl
  probability_nonneg k ω := by
    split_ifs
    · exact X.probability_nonneg k ω
    · exact le_rfl
  probability_le_one k ω := by
    split_ifs
    · exact X.probability_le_one k ω
    · exact zero_le_one
  conditional_mean k := by
    split_ifs
    · exact X.conditional_mean k
    · change μ[(0 : Ω → ℝ) | X.filtration k] =ᵐ[μ] 0
      rw [condExp_zero]
```

### truncateAt_probability

lemma; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:69)

```lean
lemma truncateAt_probability {N k : ℕ} (hk : k < N) (ω : Ω) :
    (X.truncateAt N).probability k ω = X.probability k ω
```

### truncateAt_observation

lemma; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:73)

```lean
lemma truncateAt_observation {N k : ℕ} (hk : k < N) (ω : Ω) :
    (X.truncateAt N).observation k ω = X.observation k ω
```

### truncateAt_probability_le_rowMaximum

lemma; [source line 77](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:77)

```lean
lemma truncateAt_probability_le_rowMaximum (N k : ℕ) (ω : Ω) :
    (X.truncateAt N).probability k ω ≤ X.rowMaximum N ω
```

### sum_truncateAt_probability

lemma; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:84)

```lean
lemma sum_truncateAt_probability (N : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range N, (X.truncateAt N).probability k ω) =
      ∑ k ∈ Finset.range N, X.probability k ω
```

### truncatedStop_eq_on_good

lemma; [source line 95](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:95)

On the original row's good event, zero extension and predictable
deletion preserve every observation and probability in that row.

```lean
lemma truncatedStop_eq_on_good {N k : ℕ} {δ K : ℝ} (ω : Ω)
    (hmax : X.rowMaximum N ω ≤ δ)
    (htotal : ∑ j ∈ Finset.range N, X.probability j ω ≤ K) (hk : k < N) :
    ((X.truncateAt N).stop δ K).observation k ω = X.observation k ω ∧
      ((X.truncateAt N).stop δ K).probability k ω = X.probability k ω
```

### laplaceRow

def; [source line 118](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:118)

The finite-row Laplace random variable.

```lean
noncomputable def laplaceRow (g : ℕ → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  Real.exp (-(∑ k ∈ Finset.range N, g k * X.observation k ω))

omit [IsProbabilityMeasure μ] in
```

### measurable_laplaceRow

lemma; [source line 122](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:122)

```lean
lemma measurable_laplaceRow (g : ℕ → ℝ) (N : ℕ) : Measurable (X.laplaceRow g N)
```

### laplaceRow_bounds

lemma; [source line 129](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:129)

```lean
lemma laplaceRow_bounds (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (N : ℕ) (ω : Ω) :
    0 ≤ X.laplaceRow g N ω ∧ X.laplaceRow g N ω ≤ 1
```

### integrable_laplaceRow

lemma; [source line 135](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliRow.lean:135)

```lean
lemma integrable_laplaceRow (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (N : ℕ) :
    Integrable (X.laplaceRow g N) μ
```


## Luce/Section2FiniteBernoulliSpatial.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
open scoped BigOperators NNReal
namespace Luce
variable {X : Type*} [MeasurableSpace X]
namespace FiniteAdaptedBernoulli
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {n : ℕ}
    (B : FiniteAdaptedBernoulli P n)
variable [IsProbabilityMeasure P]
```

### continuous_weightedPointMeasure

theorem; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:23)

Fixed finite locations give a continuous map from nonnegative weights
to finite measures with their weak topology.

```lean
theorem continuous_weightedPointMeasure [TopologicalSpace X] [OpensMeasurableSpace X]
    {n : ℕ} (x : Fin n → X) : Continuous (weightedPointMeasure x)
```

### pointMeasure

def; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:34)

The observed finite point measure for the finite row.

```lean
noncomputable def pointMeasure (x : Fin n → X) (ω : Ω) : FinitePointMeasure X :=
  observedPointMeasure x (fun k => B.observation k ω)
```

### predictableMeasure

def; [source line 39](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:39)

The predictable measure, using the canonical nonnegative version of
the conditional probabilities already supplied by the row adapter.

```lean
noncomputable def predictableMeasure (x : Fin n → X) (ω : Ω) : FiniteMeasure X :=
  weightedPointMeasure x (fun k =>
    (⟨B.probability k ω, B.probability_nonneg k ω⟩ : ℝ≥0))
```

### measurable_pointMeasure

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:43)

```lean
theorem measurable_pointMeasure (x : Fin n → X) : Measurable (B.pointMeasure x)
```

### measurable_predictableMeasure

theorem; [source line 47](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:47)

```lean
theorem measurable_predictableMeasure (x : Fin n → X) :
    Measurable (B.predictableMeasure x)
```

### measurableSet_predictableMeasure_preimage

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:56)

Weak-open preimages are measurable directly through the finite
coefficient vector. No Borel compatibility for the space of finite
measures is assumed.

```lean
theorem measurableSet_predictableMeasure_preimage [TopologicalSpace X]
    [OpensMeasurableSpace X] (x : Fin n → X) {U : Set (FiniteMeasure X)}
    (hU : IsOpen U) : MeasurableSet {ω | B.predictableMeasure x ω ∈ U}
```

### integral_predictableMeasure

theorem; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:65)

```lean
theorem integral_predictableMeasure (x : Fin n → X) (g : X → ℝ)
    (hg : Measurable g) (ω : Ω) :
    (∫ y, g y ∂(B.predictableMeasure x ω : Measure X)) =
      ∑ k, B.probability k ω * g (x k)
```

### spatialTest

def; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:72)

Extend a spatial test by zero outside its finite row.

```lean
def spatialTest (x : Fin n → X) (g : X → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then g (x ⟨k, h⟩) else 0

omit [MeasurableSpace X] in
```

### spatialTest_at_fin

theorem; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:76)

```lean
@[simp] theorem spatialTest_at_fin (x : Fin n → X) (g : X → ℝ) (k : Fin n) :
    spatialTest x g k.val = g (x k)
```

### spatialTest_nonneg

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:81)

```lean
theorem spatialTest_nonneg (x : Fin n → X) (g : X → ℝ)
    (hg : ∀ y, 0 ≤ g y) (k : ℕ) : 0 ≤ spatialTest x g k
```

### pointMeasure_mass

theorem; [source line 90](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:90)

```lean
theorem pointMeasure_mass (x : Fin n → X) (ω : Ω) :
    ((B.pointMeasure x ω).toFiniteMeasure.mass : ℝ) =
      ∑ k ∈ Finset.range n, B.toProcess.observation k ω
```

### predictableMeasure_mass

theorem; [source line 101](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:101)

```lean
theorem predictableMeasure_mass (x : Fin n → X) (ω : Ω) :
    ((B.predictableMeasure x ω).mass : ℝ) =
      ∑ k ∈ Finset.range n, B.toProcess.probability k ω
```

### pointLaplace_pointMeasure

theorem; [source line 115](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:115)

```lean
theorem pointLaplace_pointMeasure (x : Fin n → X) (g : X → ℝ)
    (hg : Measurable g) (ω : Ω) :
    pointLaplace g (B.pointMeasure x ω) =
      Real.exp (-(∑ k ∈ Finset.range n,
        spatialTest x g k * B.toProcess.observation k ω))
```

### laplaceCompensator_eq_integral_predictableMeasure

theorem; [source line 128](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteBernoulliSpatial.lean:128)

```lean
theorem laplaceCompensator_eq_integral_predictableMeasure (x : Fin n → X)
    (g : X → ℝ) (hg : Measurable g) (ω : Ω) :
    B.toProcess.laplaceCompensator (spatialTest x g) n ω =
      ∫ y, 1 - Real.exp (-g y) ∂(B.predictableMeasure x ω : Measure X)
```


## Luce/Section2FiniteHistoryConditional.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteHistoryConditional.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
open scoped BigOperators
namespace Luce
variable {Ω S T : Type*} {mΩ : MeasurableSpace Ω}
```

### integrable_finite_state

lemma; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteHistoryConditional.lean:20)

Any real function of a measurable finite state is integrable.

```lean
lemma integrable_finite_state (Z : Ω → S)
    (hZ : @Measurable Ω S mΩ ⊤ Z) (f : S → ℝ) :
    Integrable (fun ω => f (Z ω)) P
```

### integral_finite_state

lemma; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteHistoryConditional.lean:35)

Integration against a measurable finite state is a weighted finite sum.

```lean
lemma integral_finite_state (Z : Ω → S)
    (hZ : @Measurable Ω S mΩ ⊤ Z) (f : S → ℝ) :
    (∫ ω, f (Z ω) ∂P) = ∑ s, P.real {ω | Z ω = s} * f s
```

### condExp_finite_history

theorem; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteHistoryConditional.lean:55)

A finite-fiber integral identity characterizes conditioning on the
history of a finite state. Both finite codomains use their discrete sigma
algebras; the probability space itself is arbitrary.

```lean
theorem condExp_finite_history [Fintype T] [DecidableEq T]
    (Z : Ω → S) (hZ : @Measurable Ω S mΩ ⊤ Z)
    (H : S → T) (f : S → ℝ) (g : T → ℝ)
    (hfiber : ∀ t : T,
      (∑ s ∈ Finset.univ.filter (fun s => H s = t),
        P.real {ω | Z ω = s} * f s) =
      g t * ∑ s ∈ Finset.univ.filter (fun s => H s = t),
        P.real {ω | Z ω = s}) :
    P[(fun ω => f (Z ω)) |
      MeasurableSpace.comap (fun ω => H (Z ω)) ⊤] =ᵐ[P]
        (fun ω => g (H (Z ω)))
```

### condExp_finite_history_of_representatives

theorem; [source line 125](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FiniteHistoryConditional.lean:125)

A version of the finite-history criterion whose candidate is given on
states, is constant on history fibers, and is checked only at represented
histories. No assumption that every history is represented is needed.

```lean
theorem condExp_finite_history_of_representatives [Fintype T] [DecidableEq T]
    (Z : Ω → S) (hZ : @Measurable Ω S mΩ ⊤ Z)
    (H : S → T) (f r : S → ℝ)
    (hconst : ∀ s₁ s₂, H s₁ = H s₂ → r s₁ = r s₂)
    (hfiber : ∀ s : S,
      (∑ u ∈ Finset.univ.filter (fun u => H u = H s),
        P.real {ω | Z ω = u} * f u) =
      r s * ∑ u ∈ Finset.univ.filter (fun u => H u = H s),
        P.real {ω | Z ω = u}) :
    P[(fun ω => f (Z ω)) |
      MeasurableSpace.comap (fun ω => H (Z ω)) ⊤] =ᵐ[P]
        (fun ω => r (Z ω))
```


## Luce/Section2FinitePointMeasure.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
open scoped BigOperators Topology NNReal
namespace Luce
variable {X : Type*} [MeasurableSpace X]
namespace FinitePointMeasure
section Topology
variable [TopologicalSpace X] [OpensMeasurableSpace X]
```

### pointMeasureOfFin

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:21)

The actual finite measure associated with a finite family of points.

```lean
noncomputable def pointMeasureOfFin {m : ℕ} (x : Fin m → X) : FiniteMeasure X :=
  ∑ i, (diracProba (x i)).toFiniteMeasure
```

### finiteMeasure_mass_add

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:24)

```lean
private theorem finiteMeasure_mass_add (μ ν : FiniteMeasure X) :
    (μ + ν).mass = μ.mass + ν.mass
```

### finiteMeasure_mass_sum

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:28)

```lean
private theorem finiteMeasure_mass_sum {ι : Type*} (s : Finset ι)
    (μ : ι → FiniteMeasure X) :
    (∑ i ∈ s, μ i).mass = ∑ i ∈ s, (μ i).mass
```

### pointMeasureOfFin_mass

theorem; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:36)

```lean
@[simp] theorem pointMeasureOfFin_mass {m : ℕ} (x : Fin m → X) :
    (pointMeasureOfFin x).mass = m
```

### FinitePointMeasure

def; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:41)

Finite point measures, represented as measures rather than labeled lists.

```lean
def FinitePointMeasure (X : Type*) [MeasurableSpace X] :=
  {μ : FiniteMeasure X // ∃ (m : ℕ) (x : Fin m → X), pointMeasureOfFin x = μ}
```

### instance at line 46

instance; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:46)

```lean
instance : MeasurableSpace (FinitePointMeasure X) :=
  inferInstanceAs (MeasurableSpace {μ : FiniteMeasure X //
    ∃ (m : ℕ) (x : Fin m → X), pointMeasureOfFin x = μ})
```

### toFiniteMeasure

def; [source line 51](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:51)

Forget only the proof of finite counting-measure representability.

```lean
def toFiniteMeasure (μ : FinitePointMeasure X) : FiniteMeasure X := μ.val
```

### instance at line 53

instance; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:53)

```lean
instance : Coe (FinitePointMeasure X) (FiniteMeasure X) := ⟨toFiniteMeasure⟩
```

### ofFin

def; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:56)

The measure represented by a finite family; repeated points are retained.

```lean
noncomputable def ofFin {m : ℕ} (x : Fin m → X) : FinitePointMeasure X :=
  ⟨pointMeasureOfFin x, m, x, rfl⟩
```

### instance at line 59

instance; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:59)

```lean
instance : Zero (FinitePointMeasure X) :=
  ⟨⟨0, 0, Fin.elim0, by simp [pointMeasureOfFin]⟩⟩
```

### toFiniteMeasure_ofFin

theorem; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:62)

```lean
@[simp] theorem toFiniteMeasure_ofFin {m : ℕ} (x : Fin m → X) :
    (ofFin x).toFiniteMeasure = pointMeasureOfFin x
```

### toFiniteMeasure_zero

theorem; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:65)

```lean
@[simp] theorem toFiniteMeasure_zero :
    (0 : FinitePointMeasure X).toFiniteMeasure = 0
```

### count

def; [source line 70](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:70)

Counts on a measurable set; the finite Dirac representation makes this
an actual natural-number count.

```lean
noncomputable def count (μ : FinitePointMeasure X) (B : Set X) : ℕ :=
  Nat.floor (μ.toFiniteMeasure B : ℝ)
```

### ofFin_mass

theorem; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:73)

```lean
@[simp] theorem ofFin_mass {m : ℕ} (x : Fin m → X) :
    (ofFin x).toFiniteMeasure.mass = m
```

### measurable_toFiniteMeasure

theorem; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:76)

```lean
theorem measurable_toFiniteMeasure :
    Measurable (toFiniteMeasure : FinitePointMeasure X → FiniteMeasure X)
```

### measurable_toMeasure

theorem; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:80)

```lean
theorem measurable_toMeasure :
    Measurable (fun μ : FinitePointMeasure X => (μ.toFiniteMeasure : Measure X))
```

### measurable_count

theorem; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:84)

```lean
theorem measurable_count {B : Set X} (hB : MeasurableSet B) :
    Measurable (fun μ : FinitePointMeasure X => μ.count B)
```

### measurable_ofFin

theorem; [source line 89](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:89)

```lean
theorem measurable_ofFin {m : ℕ} :
    Measurable (ofFin : (Fin m → X) → FinitePointMeasure X)
```

### instance at line 102

instance; [source line 102](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:102)

```lean
instance : TopologicalSpace (FinitePointMeasure X) :=
  inferInstanceAs (TopologicalSpace {μ : FiniteMeasure X //
    ∃ (m : ℕ) (x : Fin m → X), pointMeasureOfFin x = μ})
```

### continuous_toFiniteMeasure

theorem; [source line 106](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:106)

```lean
theorem continuous_toFiniteMeasure :
    Continuous (toFiniteMeasure : FinitePointMeasure X → FiniteMeasure X)
```

### continuous_ofFin

theorem; [source line 110](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:110)

```lean
theorem continuous_ofFin {m : ℕ} :
    Continuous (ofFin : (Fin m → X) → FinitePointMeasure X)
```

### isCompact_mass_le

theorem; [source line 120](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePointMeasure.lean:120)

The finite count bound is compact for literal open-cover compactness;
no Hausdorff condition on the original spatial space is needed.

```lean
theorem isCompact_mass_le [CompactSpace X] (N : ℕ) :
    IsCompact {μ : FinitePointMeasure X | μ.toFiniteMeasure.mass ≤ N}
```


## Luce/Section2FinitePoissonLaw.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
namespace Luce
variable {X : Type*} [MeasurableSpace X]
```

### integral_pointMeasureOfFin

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:20)

```lean
theorem integral_pointMeasureOfFin {m : ℕ} (x : Fin m → X)
    (g : X → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂(pointMeasureOfFin x : Measure X)) = ∑ i, g (x i)
```

### integrable_pointMeasure

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:28)

```lean
theorem integrable_pointMeasure (μ : FinitePointMeasure X)
    (g : X → ℝ) (hg : Measurable g) :
    Integrable g (μ.toFiniteMeasure : Measure X)
```

### pointLaplace

def; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:40)

The ordinary Laplace test on an actual finite point measure.

```lean
noncomputable def pointLaplace (g : X → ℝ) (μ : FinitePointMeasure X) : ℝ :=
  Real.exp (-(∫ x, g x ∂(μ.toFiniteMeasure : Measure X)))
```

### measurable_pointLaplace

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:43)

```lean
theorem measurable_pointLaplace (g : X → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) : Measurable (pointLaplace g)
```

### pointLaplace_mem_Icc

theorem; [source line 58](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:58)

```lean
theorem pointLaplace_mem_Icc (g : X → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (μ : FinitePointMeasure X) : 0 ≤ pointLaplace g μ ∧ pointLaplace g μ ≤ 1
```

### pointLaplace_zero

theorem; [source line 63](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:63)

```lean
@[simp] theorem pointLaplace_zero (g : X → ℝ) :
    pointLaplace g (0 : FinitePointMeasure X) = 1
```

### pointLaplace_ofFin

theorem; [source line 67](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:67)

```lean
theorem pointLaplace_ofFin {m : ℕ} (x : Fin m → X)
    (g : X → ℝ) (hg : Measurable g) :
    pointLaplace g (FinitePointMeasure.ofFin x) = ∏ i, Real.exp (-g (x i))
```

### iidPointLaw

def; [source line 74](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:74)

The point measure of `m` independent samples with common probability law `p`.

```lean
noncomputable def iidPointLaw (p : ProbabilityMeasure X) (m : ℕ) :
    Measure (FinitePointMeasure X) :=
  (Measure.pi fun _ : Fin m => (p : Measure X)).map FinitePointMeasure.ofFin
```

### instance at line 78

instance; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:78)

```lean
instance iidPointLaw_isProbabilityMeasure (p : ProbabilityMeasure X) (m : ℕ) :
    IsProbabilityMeasure (iidPointLaw p m) :=
  Measure.isProbabilityMeasure_map FinitePointMeasure.measurable_ofFin.aemeasurable
```

### integral_pointLaplace_iidPointLaw

theorem; [source line 82](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:82)

```lean
theorem integral_pointLaplace_iidPointLaw (p : ProbabilityMeasure X) (m : ℕ)
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ μ, pointLaplace g μ ∂iidPointLaw p m) =
      (∫ x, Real.exp (-g x) ∂(p : Measure X)) ^ m
```

### nonempty_of_finiteMeasure_ne_zero

theorem; [source line 93](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:93)

```lean
private theorem nonempty_of_finiteMeasure_ne_zero (ν : FiniteMeasure X) (hν : ν ≠ 0) :
    Nonempty X
```

### finitePoissonLaw

def; [source line 102](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:102)

A finite-intensity Poisson law, constructed by a Poisson count and iid
locations. The zero law is defined even when the underlying space is empty.

```lean
noncomputable def finitePoissonLaw (ν : FiniteMeasure X) :
    Measure (FinitePointMeasure X) := by
  classical
  exact if hν : ν = 0 then Measure.dirac 0 else
    letI := nonempty_of_finiteMeasure_ne_zero ν hν
    poissonMixture ν.mass (iidPointLaw ν.normalize)
```

### finitePoissonLaw_zero

theorem; [source line 109](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:109)

```lean
@[simp] theorem finitePoissonLaw_zero :
    finitePoissonLaw (0 : FiniteMeasure X) = Measure.dirac 0
```

### finitePoissonLaw_of_ne_zero

theorem; [source line 113](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:113)

```lean
theorem finitePoissonLaw_of_ne_zero [Nonempty X] (ν : FiniteMeasure X) (hν : ν ≠ 0) :
    finitePoissonLaw ν = poissonMixture ν.mass (iidPointLaw ν.normalize)
```

### instance at line 117

instance; [source line 117](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:117)

```lean
instance finitePoissonLaw_isProbabilityMeasure (ν : FiniteMeasure X) :
    IsProbabilityMeasure (finitePoissonLaw ν) := by
  classical
  by_cases hν : ν = 0
  · subst ν
    rw [finitePoissonLaw_zero]
    infer_instance
  · let := nonempty_of_finiteMeasure_ne_zero ν hν
    rw [finitePoissonLaw_of_ne_zero ν hν]
    infer_instance
```

### integrable_exp_neg

theorem; [source line 128](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:128)

```lean
theorem integrable_exp_neg (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    Integrable (fun x => Real.exp (-g x)) μ
```

### integrable_one_sub_exp_neg

theorem; [source line 136](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:136)

```lean
theorem integrable_one_sub_exp_neg (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    Integrable (fun x => 1 - Real.exp (-g x)) μ
```

### integral_exp_neg_mem_Icc

theorem; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:141)

```lean
theorem integral_exp_neg_mem_Icc (p : ProbabilityMeasure X)
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    0 ≤ (∫ x, Real.exp (-g x) ∂(p : Measure X)) ∧
      (∫ x, Real.exp (-g x) ∂(p : Measure X)) ≤ 1
```

### integral_one_sub_exp_neg_eq_mass_mul

theorem; [source line 152](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:152)

```lean
theorem integral_one_sub_exp_neg_eq_mass_mul [Nonempty X]
    (ν : FiniteMeasure X) (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x, (1 - Real.exp (-g x)) ∂(ν : Measure X)) =
      (ν.mass : ℝ) * (1 - ∫ x, Real.exp (-g x) ∂(ν.normalize : Measure X))
```

### integrable_pointLaplace_finitePoissonLaw

theorem; [source line 170](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:170)

```lean
theorem integrable_pointLaplace_finitePoissonLaw (ν : FiniteMeasure X)
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    Integrable (pointLaplace g) (finitePoissonLaw ν)
```

### integral_pointLaplace_finitePoissonLaw

theorem; [source line 183](D:/princeton/Research/Lean/Lean_luce/Luce/Section2FinitePoissonLaw.lean:183)

The Laplace functional of the finite-intensity Poisson iid construction.
The intensity may vanish and the spatial measurable space may be empty.
Every measurable nonnegative real test is allowed; its intensity integral
need not be finite. The integrand on the right is automatically bounded.

```lean
theorem integral_pointLaplace_finitePoissonLaw (ν : FiniteMeasure X)
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ μ, pointLaplace g μ ∂finitePoissonLaw ν) =
      Real.exp (-(∫ x, (1 - Real.exp (-g x)) ∂(ν : Measure X)))
```


## Luce/Section1FirstChoice.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section1FirstChoice.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace Luce
```

### backgroundSurvivors_eq_all

lemma; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section1FirstChoice.lean:12)

```lean
lemma backgroundSurvivors_eq_all {n : ℕ} (t : ℝ) (background : Fin n → ℝ) :
    backgroundSurvivors t background = n ↔ ∀ j, t < background j
```

### background_all_probability

lemma; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section1FirstChoice.lean:22)

The probability that all background clocks survive is the product of
their exponential survival functions.

```lean
lemma background_all_probability {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (t : ℝ) (ht : 0 ≤ t) :
    (backgroundRace w i).real {background | backgroundSurvivors t background = n} =
      Real.exp (-(∑ j, w.rate (i.succAbove j)) * t)
```

### exponentialRace_first_choice

theorem; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section1FirstChoice.lean:42)

A label wins an independent exponential race with probability equal to
its weight divided by the total weight, the Luce choice rule.

```lean
theorem exponentialRace_first_choice {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) :
    (exponentialRace w).real {clocks | raceRank clocks i = 1} =
      w.rate i / w.total Finset.univ
```


## Luce/Section2HistoryAtoms.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryAtoms.lean)

Namespace / shared context (consult source for section boundaries):

```lean
namespace Luce
```

### prefixVector

def; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryAtoms.lean:15)

The complete vector of the first `m` draws.

```lean
def prefixVector {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    {j : Fin n // j.val < m} → Fin n := fun j => σ j.val
```

### drawHistory_eq_comap_prefixVector

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryAtoms.lean:20)

The approved sigma algebra is exactly that generated by the finite
prefix vector, whose codomain carries the discrete sigma algebra.

```lean
theorem drawHistory_eq_comap_prefixVector {Ω : Type*} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) :
    drawHistory π m = MeasurableSpace.comap (fun ω => prefixVector (π ω) m) ⊤
```

### prefixVector_eq_iff

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryAtoms.lean:33)

The finite prefix vectors are equal exactly when all corresponding
preceding draws agree.

```lean
theorem prefixVector_eq_iff {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (m : ℕ) :
    prefixVector σ m = prefixVector τ m ↔
      ∀ j : Fin n, j.val < m → σ j = τ j
```

### remaining_eq_of_prefix_agreement

theorem; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryAtoms.lean:44)

Availability of every label is fixed by the preceding draw vector.

```lean
theorem remaining_eq_of_prefix_agreement {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (k : Fin n) (hprefix : ∀ j : Fin n, j < k → σ j = τ j) :
    remaining σ k = remaining τ k
```

### predictableChance_eq_of_prefix_agreement

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryAtoms.lean:56)

The proportional chance is constant on each atom of the preceding
draw history.

```lean
theorem predictableChance_eq_of_prefix_agreement {n : ℕ} (w : Weights n)
    (σ τ : Equiv.Perm (Fin n)) (k : Fin n)
    (hprefix : ∀ j : Fin n, j < k → σ j = τ j) :
    predictableChance w σ k = predictableChance w τ k
```


## Luce/Section2HistoryPredictability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryPredictability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
universe u
namespace Luce
```

### measurable_draw_of_lt

lemma; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryPredictability.lean:20)

Each already observed coordinate is measurable for the draw history.

```lean
lemma measurable_draw_of_lt {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) {m : ℕ} (j : Fin n) (hj : j.val < m) :
    Measurable[drawHistory π m, (⊤ : MeasurableSpace (Fin n))] (fun ω => π ω j)
```

### measurableSet_label_available

lemma; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryPredictability.lean:28)

Any label remains precisely when no preceding draw has selected it.
This supplies the measurable summands in the remaining-weight formula.

```lean
lemma measurableSet_label_available {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (k i : Fin n) :
    MeasurableSet[drawHistory π k.val] {ω | k ≤ (π ω).symm i}
```

### measurable_availability_indicator

lemma; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryPredictability.lean:46)

The availability indicator is measurable before draw `k.val + 1`.

```lean
lemma measurable_availability_indicator {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (k : Fin n) :
    Measurable[drawHistory π k.val]
      (fun ω => if k ≤ (π ω).symm k then (1 : ℝ) else 0)
```

### measurable_remaining_weight

lemma; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryPredictability.lean:53)

The remaining weight is measurable for exactly the same pre-draw history.

```lean
lemma measurable_remaining_weight {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (k : Fin n) :
    Measurable[drawHistory π k.val]
      (fun ω => w.total (remaining (π ω) k))
```

### history_predictability

theorem; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section2HistoryPredictability.lean:64)

The exact approved Section 2 predictability statement.

```lean
theorem history_predictability {Ω : Type u} {n : ℕ} (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n)) (k : Fin n) :
    Measurable[drawHistory π k.val]
      (fun ω => if k ≤ (π ω).symm k then (1 : ℝ) else 0) ∧
    Measurable[drawHistory π k.val]
      (fun ω => w.total (remaining (π ω) k))
```


## Luce/Section3Interior.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
section Variance
variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
```

### monotone_bracket_error

theorem; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean:22)

Monotonicity turns two grid-point bounds and two bounds on the limiting
function's oscillation into a bound at every intervening point.

```lean
theorem monotone_bracket_error {f g : ℝ → ℝ} (hg : Monotone g)
    {a t b ε δ : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (ha : |g a - f a| ≤ ε) (hb : |g b - f b| ≤ ε)
    (hfa : |f t - f a| ≤ δ) (hfb : |f b - f t| ≤ δ) :
    |g t - f t| ≤ ε + δ
```

### monotone_grid_error

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean:33)

The finite-grid upgrade used for the empirical arrival distribution.

```lean
theorem monotone_grid_error {f g : ℝ → ℝ} (hg : Monotone g)
    (grid : Finset ℝ) (domain : Set ℝ) {ε δ : ℝ}
    (hgrid : ∀ t ∈ grid, |g t - f t| ≤ ε)
    (hcover : ∀ t ∈ domain, ∃ a ∈ grid, ∃ b ∈ grid,
      a ≤ t ∧ t ≤ b ∧ |f t - f a| ≤ δ ∧ |f b - f t| ≤ δ) :
    ∀ t ∈ domain, |g t - f t| ≤ ε + δ
```

### antitone_bracket_error

theorem; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean:44)

The same grid argument for decreasing remaining-rate functions.

```lean
theorem antitone_bracket_error {f g : ℝ → ℝ} (hg : Antitone g)
    {a t b ε δ : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (ha : |g a - f a| ≤ ε) (hb : |g b - f b| ≤ ε)
    (hfa : |f t - f a| ≤ δ) (hfb : |f b - f t| ≤ δ) :
    |g t - f t| ≤ ε + δ
```

### sum_sq_le_max_mul_sum

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean:56)

The weight sum of squares is controlled by the largest weight times
the total weight.

```lean
theorem sum_sq_le_max_mul_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) {M : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hM : ∀ i ∈ s, w i ≤ M) :
    ∑ i ∈ s, (w i)^2 ≤ M * ∑ i ∈ s, w i
```

### normalized_sum_sq_le

theorem; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean:65)

The deterministic estimate behind the remaining-rate variance bound.

```lean
theorem normalized_sum_sq_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) {M N : ℝ}
    (hN : 0 < N) (hw : ∀ i ∈ s, 0 ≤ w i) (hM : ∀ i ∈ s, w i ≤ M)
    (hsum : ∑ i ∈ s, w i = N) :
    (∑ i ∈ s, (w i)^2) / N^2 ≤ M / N
```

### variance_normalized_sum_le

theorem; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean:80)

Independent variables with the weight-square variance bounds satisfy
the precise normalized variance estimate used in the race law.

```lean
theorem variance_normalized_sum_le (s : Finset ι) (X : ι → Ω → ℝ)
    (w : ι → ℝ) {M N : ℝ} (hN : 0 < N)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hM : ∀ i ∈ s, w i ≤ M)
    (hsum : ∑ i ∈ s, w i = N)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hind : Set.Pairwise ↑s fun i j => IndepFun (X i) (X j) μ)
    (hvar : ∀ i ∈ s, variance (X i) μ ≤ (w i)^2) :
    variance (fun ω => (∑ i ∈ s, X i ω) / N) μ ≤ M / N
```

### denominator_lower_bound

theorem; [source line 105](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean:105)

A positive deterministic denominator remains bounded away from zero
when the empirical denominator is sufficiently close.

```lean
theorem denominator_lower_bound {D W d : ℝ} (hdD : d ≤ D)
    (herror : |W - D| ≤ d / 2) : d / 2 ≤ W
```

### probability_le_of_denominator_close

theorem; [source line 111](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean:111)

The maximum predictable probability estimate on the good race event.

```lean
theorem probability_le_of_denominator_close {w D W d : ℝ}
    (hw : 0 ≤ w) (hd : 0 < d) (hdD : d ≤ D) (herror : |W - D| ≤ d / 2) :
    w / W ≤ 2 * w / d
```

### abs_div_sub_div_le

theorem; [source line 120](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean:120)

Quantitative denominator replacement in the interior compensator.

```lean
theorem abs_div_sub_div_le {w D W d ε : ℝ} (hw : 0 ≤ w) (hd : 0 < d)
    (hdD : d ≤ D) (hdW : d ≤ W) (herror : |W - D| ≤ ε) :
    |w / W - w / D| ≤ w * ε / d^2
```

### random_time_substitution_bound

theorem; [source line 137](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Interior.lean:137)

Evaluation at perturbed times splits into the uniform race error and
the deterministic continuity error.

```lean
theorem random_time_substitution_bound {D Dhat : ℝ → ℝ}
    {t τ ε δ : ℝ} (hrace : |Dhat τ - D τ| ≤ ε) (htime : |D τ - D t| ≤ δ) :
    |Dhat τ - D t| ≤ ε + δ
```


## Luce/Section4LaplaceCountTightness.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4LaplaceCountTightness.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Luce
section PointMeasures
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
```

### laplace_gap_tail_bound

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section4LaplaceCountTightness.lean:19)

Markov's inequality for the bounded Laplace gap, with no first-moment
assumption on the nonnegative random variable.

```lean
theorem laplace_gap_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    {t : ℝ} (ht : 0 < t) (N : ℕ) (hN : 1 ≤ t * N) :
    (1 - Real.exp (-1)) * P.real {ω | (N : ℝ) < Y ω} ≤
      1 - ∫ ω, Real.exp (-t * Y ω) ∂P
```

### nonneg_laplace_tightness

theorem; [source line 51](D:/princeton/Research/Lean/Lean_luce/Luce/Section4LaplaceCountTightness.lean:51)

Laplace convergence to a transform continuous at zero forces eventual
tightness of any row of nonnegative random variables.

```lean
theorem nonneg_laplace_tightness
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Y : ∀ n, Ω n → ℝ) (hY : ∀ n, Measurable (Y n))
    (hY0 : ∀ n ω, 0 ≤ Y n ω) (L : ℝ → ℝ)
    (hLaplace : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => ∫ ω, Real.exp (-t * Y n ω) ∂P n) atTop (𝓝 (L t)))
    (hL : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ n in atTop,
      (P n).real {ω | (N : ℝ) < Y n ω} < ε
```

### nonneg_laplace_tendsto_zero

theorem; [source line 83](D:/princeton/Research/Lean/Lean_luce/Luce/Section4LaplaceCountTightness.lean:83)

The Laplace transform of a proper law of finite nonnegative variables
is right-continuous at zero, independently of its expectation.

```lean
theorem nonneg_laplace_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) :
    Tendsto (fun t : ℝ => ∫ ω, Real.exp (-t * Y ω) ∂P)
      (𝓝[>] (0 : ℝ)) (𝓝 1)
```

### momentLaplace_const_pointMoment

theorem; [source line 110](D:/princeton/Research/Lean/Lean_luce/Luce/Section4LaplaceCountTightness.lean:110)

The constant Laplace coordinate is the ordinary total-mass Laplace test.

```lean
theorem momentLaplace_const_pointMoment (t : ℝ≥0) (ξ : FinitePointMeasure X) :
    momentLaplace (BoundedContinuousFunction.const X t) (pointMoment ξ) =
      Real.exp (-(t : ℝ) * (ξ.toFiniteMeasure.mass : ℝ))
```

### pointMeasure_tightness_of_laplace

theorem; [source line 123](D:/princeton/Research/Lean/Lean_luce/Luce/Section4LaplaceCountTightness.lean:123)

Laplace convergence to any probability law on finite point measures
already supplies the total-count tightness required by the law-convergence
theorem. No expected-mass convergence or integrability is assumed.

```lean
theorem pointMeasure_tightness_of_laplace
    (μ : ℕ → Measure (FinitePointMeasure X)) (Q : Measure (FinitePointMeasure X))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure Q]
    (hLaplace : ∀ g : X →ᵇ ℝ≥0,
      Tendsto (fun n => ∫ ξ, momentLaplace g (pointMoment ξ) ∂μ n) atTop
        (𝓝 (∫ ξ, momentLaplace g (pointMoment ξ) ∂Q))) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ n in atTop,
      (μ n).real {ξ | (N : ℝ≥0) < ξ.toFiniteMeasure.mass} < ε
```


## Luce/Section2LikelihoodSecondMoment.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LikelihoodSecondMoment.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
open scoped BigOperators
namespace Luce.BernoulliProcess
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
```

### likelihood_bounds_of_terminal_cap

lemma; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LikelihoodSecondMoment.lean:23)

```lean
private lemma likelihood_bounds_of_terminal_cap {δ K : ℝ} (hδ : δ < 1)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ)
    (hK : ∀ ω, ∑ k ∈ Finset.range N, X.probability k ω ≤ K)
    {m : ℕ} (hm : m ≤ N) (ω : Ω) :
    0 ≤ X.likelihood g m ω ∧
      X.likelihood g m ω ≤ Real.exp (K / (1 - δ))
```

### integrable_likelihood_sq

theorem; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LikelihoodSecondMoment.lean:35)

The capped likelihood has an integrable square at every prefix.

```lean
theorem integrable_likelihood_sq {δ K : ℝ} (hδ : δ < 1)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ)
    (hK : ∀ ω, ∑ k ∈ Finset.range N, X.probability k ω ≤ K)
    {m : ℕ} (hm : m ≤ N) :
    Integrable (fun ω => (X.likelihood g m ω) ^ 2) μ
```

### integral_likelihood_sq_le

theorem; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LikelihoodSecondMoment.lean:53)

Uniform second-moment estimate in the manuscript's form
`E[L_m²] ≤ exp(Cδ * K)`, with `Cδ = 1 / (1 - δ)`.
The decisive estimate is the pointwise `L_m² ≤ exp(K/(1-δ)) * L_m`,
followed by the mean-one identity.

```lean
theorem integral_likelihood_sq_le {δ K : ℝ} (hδ : δ < 1)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hpδ : ∀ k ω, X.probability k ω ≤ δ) (N : ℕ)
    (hK : ∀ ω, ∑ k ∈ Finset.range N, X.probability k ω ≤ K)
    {m : ℕ} (hm : m ≤ N) :
    (∫ ω, (X.likelihood g m ω) ^ 2 ∂μ) ≤ Real.exp (K / (1 - δ))
```

### stopped_integral_likelihood_sq_le

theorem; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LikelihoodSecondMoment.lean:73)

The manuscript's predictable deletion construction supplies the caps,
so the second-moment bound is uniform over every time of a stopped row.

```lean
theorem stopped_integral_likelihood_sq_le {δ K : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) (hK : 0 ≤ K) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (m : ℕ) :
    (∫ ω, ((X.stop δ K).likelihood g m ω) ^ 2 ∂μ) ≤
      Real.exp (K / (1 - δ))
```


## Luce/Section2LuceMassRecursion.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LuceMassRecursion.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
namespace Luce.Weights
```

### removeFirst

def; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LuceMassRecursion.lean:9)

Weights remaining after selecting `p`, relabelled by swapping `p` with zero.

```lean
def removeFirst {n : ℕ} (w : Weights (n + 1)) (p : Fin (n + 1)) : Weights n where
  rate i := w.rate (Equiv.swap 0 p i.succ)
  positive _i := w.positive _
```

### sum_rate_perm

lemma; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LuceMassRecursion.lean:13)

```lean
lemma sum_rate_perm {n : ℕ} (w : Weights n) (π : Equiv.Perm (Fin n)) :
    (∑ j, w.rate (π j)) = w.total Finset.univ
```

### decomposeFin_tail_sum

lemma; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LuceMassRecursion.lean:17)

```lean
lemma decomposeFin_tail_sum {n : ℕ} (w : Weights (n + 1))
    (p : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (r : Fin n) :
    (∑ j ∈ Finset.univ.filter (r.succ ≤ ·),
      w.rate (Equiv.Perm.decomposeFin.symm (p, τ) j)) =
    ∑ j ∈ Finset.univ.filter (r ≤ ·), (w.removeFirst p).rate (τ j)
```

### mass_decomposeFin

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LuceMassRecursion.lean:27)

Splitting a Luce permutation mass into its first draw and remaining mass.

```lean
theorem mass_decomposeFin {n : ℕ} (w : Weights (n + 1))
    (p : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    w.mass (Equiv.Perm.decomposeFin.symm (p, τ)) =
      (w.rate p / w.total Finset.univ) * (w.removeFirst p).mass τ
```

### sum_mass

theorem; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LuceMassRecursion.lean:41)

The defining Luce masses sum to one over all permutations.

```lean
theorem sum_mass {n : ℕ} (w : Weights n) :
    ∑ τ : Equiv.Perm (Fin n), w.mass τ = 1
```


## Luce/Section2LuceNextDraw.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LuceNextDraw.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
open Classical
namespace Luce
```

### prefixAgrees_succ_iff

lemma; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LuceNextDraw.lean:16)

```lean
lemma prefixAgrees_succ_iff {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (k : Fin n) :
    prefixAgrees σ τ (k.val + 1) ↔
      prefixAgrees σ τ k.val ∧ σ k = τ k
```

### sum_mass_prefix_next

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LuceNextDraw.lean:28)

Total mass of all completions with a specified next draw.

```lean
theorem sum_mass_prefix_next {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (k i : Fin n) :
    (∑ τ : Equiv.Perm (Fin n),
      if prefixAgrees σ τ k.val ∧ τ k = i then w.mass τ else 0) =
      w.choice (remaining σ k) i * prefixMass w σ k.val
```

### fixed_point_mass_fiber_identity

theorem; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LuceNextDraw.lean:68)

The finite history-fiber identity for the fixed-point indicator.

```lean
theorem fixed_point_mass_fiber_identity {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    (∑ τ ∈ Finset.univ.filter
        (fun τ : Equiv.Perm (Fin n) => prefixVector τ k.val = prefixVector σ k.val),
      w.mass τ * (if τ.symm k = k then (1 : ℝ) else 0)) =
      predictableChance w σ k *
        ∑ τ ∈ Finset.univ.filter
          (fun τ : Equiv.Perm (Fin n) => prefixVector τ k.val = prefixVector σ k.val),
          w.mass τ
```


## Luce/Section2LucePrefixMass.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixMass.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
open Classical
namespace Luce
```

### sum_mass_prefix

theorem; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixMass.lean:10)

Summing the defining permutation masses over all completions of a prefix
gives exactly its truncated Luce product.

```lean
theorem sum_mass_prefix {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n) :
    (∑ τ : Equiv.Perm (Fin n), if prefixAgrees σ τ m then w.mass τ else 0) =
      prefixMass w σ m
```


## Luce/Section2LucePrefixRecursion.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixRecursion.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
namespace Luce
```

### prefixAgrees

def; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixRecursion.lean:14)

Agreement on precisely the first `m` draw positions.

```lean
def prefixAgrees {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (m : ℕ) : Prop :=
  ∀ j : Fin n, j.val < m → σ j = τ j
```

### prefixMass

def; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixRecursion.lean:18)

The product of the first `m` factors in the defining Luce mass.

```lean
noncomputable def prefixMass {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.univ.filter (fun r : Fin n => r.val < m),
    w.rate (σ r) / ∑ j ∈ Finset.univ.filter (r ≤ ·), w.rate (σ j)
```

### prefixAgrees_zero

lemma; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixRecursion.lean:23)

```lean
lemma prefixAgrees_zero {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : prefixAgrees σ τ 0
```

### prefixAgrees_self

lemma; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixRecursion.lean:26)

```lean
lemma prefixAgrees_self {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    prefixAgrees σ σ m
```

### prefixMass_zero

lemma; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixRecursion.lean:29)

```lean
lemma prefixMass_zero {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n)) :
    prefixMass w σ 0 = 1
```

### prefixMass_full

lemma; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixRecursion.lean:32)

```lean
lemma prefixMass_full {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n)) :
    prefixMass w σ n = w.mass σ
```

### prefixAgrees_decomposeFin

lemma; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixRecursion.lean:36)

Removing the first draw leaves the same agreement condition on the tail.

```lean
lemma prefixAgrees_decomposeFin {n : ℕ} (p q : Fin (n + 1))
    (σ τ : Equiv.Perm (Fin n)) (m : ℕ) :
    prefixAgrees (Equiv.Perm.decomposeFin.symm (p, σ))
      (Equiv.Perm.decomposeFin.symm (q, τ)) (m + 1) ↔
      p = q ∧ prefixAgrees σ τ m
```

### prefixMass_decomposeFin

lemma; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixRecursion.lean:56)

The first partial-product factor splits off with the same reduced weights
as the full Luce mass.

```lean
lemma prefixMass_decomposeFin {n : ℕ} (w : Weights (n + 1))
    (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    prefixMass w (Equiv.Perm.decomposeFin.symm (p, σ)) (m + 1) =
      (w.rate p / w.total Finset.univ) * prefixMass (w.removeFirst p) σ m
```


## Luce/Section2LucePrefixTransition.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixTransition.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
namespace Luce
```

### remaining_total_eq_tail_sum

theorem; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixTransition.lean:15)

```lean
theorem remaining_total_eq_tail_sum {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    w.total (remaining σ k) =
      ∑ j ∈ Finset.univ.filter (k ≤ ·), w.rate (σ j)
```

### prefixMass_succ

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixTransition.lean:24)

```lean
theorem prefixMass_succ {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    prefixMass w σ (k.val + 1) =
      prefixMass w σ k.val * (w.rate (σ k) / w.total (remaining σ k))
```

### prefixMass_eq_of_prefix_agreement

theorem; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixTransition.lean:42)

Agreement on the prefix fixes every factor in its partial Luce mass.
The identity holds even when `m ≥ n`, since both prefixes then include all
draw positions.

```lean
theorem prefixMass_eq_of_prefix_agreement {n : ℕ} (w : Weights n)
    (σ τ : Equiv.Perm (Fin n)) (m : ℕ) (hprefix : prefixAgrees σ τ m) :
    prefixMass w σ m = prefixMass w τ m
```

### exists_prefixAgrees_next_eq

theorem; [source line 57](D:/princeton/Research/Lean/Lean_luce/Luce/Section2LucePrefixTransition.lean:57)

Any available label can be chosen next while preserving all preceding
draws. The representative is obtained by swapping that label with the
current next label in the output of the permutation.

```lean
theorem exists_prefixAgrees_next_eq {n : ℕ} (σ : Equiv.Perm (Fin n))
    (k i : Fin n) (havailable : k ≤ σ.symm i) :
    ∃ τ : Equiv.Perm (Fin n), prefixAgrees σ τ k.val ∧ τ k = i
```


## Luce/Section1Model.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
namespace Luce
namespace Weights
variable {n : ℕ} (w : Weights n)
```

### Weights

structure; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:22)

A finite family of strictly positive Luce weights.

```lean
structure Weights (n : ℕ) where
  rate : Fin n → ℝ
  positive : ∀ i, 0 < rate i
```

### scale

def; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:31)

Multiplying every rate by the same positive constant.

```lean
def scale (c : ℝ) (hc : 0 < c) : Weights n where
  rate i := c * w.rate i
  positive i := mul_pos hc (w.positive i)
```

### total

def; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:36)

Total weight of a set of remaining labels.

```lean
noncomputable def total (s : Finset (Fin n)) : ℝ := ∑ i ∈ s, w.rate i
```

### total_nonneg

lemma; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:38)

```lean
lemma total_nonneg (s : Finset (Fin n)) : 0 ≤ w.total s
```

### total_pos

lemma; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:41)

```lean
lemma total_pos {s : Finset (Fin n)} (hs : s.Nonempty) : 0 < w.total s
```

### rate_le_total

lemma; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:44)

```lean
lemma rate_le_total {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) :
    w.rate i ≤ w.total s
```

### choice

def; [source line 49](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:49)

Proportional choice from a finite set; a removed label has chance zero.

```lean
noncomputable def choice (s : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ s then w.rate i / w.total s else 0
```

### choice_nonneg

lemma; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:52)

```lean
lemma choice_nonneg (s : Finset (Fin n)) (i : Fin n) : 0 ≤ w.choice s i
```

### choice_le_one

lemma; [source line 58](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:58)

```lean
lemma choice_le_one (s : Finset (Fin n)) (i : Fin n) : w.choice s i ≤ 1
```

### sum_choice

lemma; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:64)

```lean
lemma sum_choice {s : Finset (Fin n)} (hs : s.Nonempty) :
    ∑ i, w.choice s i = 1
```

### total_scale

lemma; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:72)

```lean
lemma total_scale (c : ℝ) (hc : 0 < c) (s : Finset (Fin n)) :
    (w.scale c hc).total s = c * w.total s
```

### choice_scale

lemma; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:76)

```lean
lemma choice_scale (c : ℝ) (hc : 0 < c) (s : Finset (Fin n)) (i : Fin n) :
    (w.scale c hc).choice s i = w.choice s i
```

### mass

def; [source line 86](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:86)

Equation `eq:luce-law`, with zero-based labels and positions.

```lean
noncomputable def mass (π : Equiv.Perm (Fin n)) : ℝ :=
  ∏ r, w.rate (π r) / ∑ j ∈ Finset.univ.filter (r ≤ ·), w.rate (π j)
```

### mass_pos

lemma; [source line 89](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:89)

```lean
lemma mass_pos (π : Equiv.Perm (Fin n)) : 0 < w.mass π
```

### mass_scale

lemma; [source line 97](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:97)

```lean
lemma mass_scale (c : ℝ) (hc : 0 < c) (π : Equiv.Perm (Fin n)) :
    (w.scale c hc).mass π = w.mass π
```

### remaining

def; [source line 108](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:108)

Labels that have not been drawn immediately before position `k`.

```lean
def remaining {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => k ≤ π.symm i
```

### inverse_fixed_iff

lemma; [source line 112](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:112)

The draw order and its inverse have exactly the same fixed labels.

```lean
lemma inverse_fixed_iff {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    π.symm i = i ↔ π i = i
```

### fixedCount

def; [source line 123](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:123)

Equation `eq:fixed-process`: total number of fixed labels.

```lean
def fixedCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i => π i = i).card
```

### fixedCount_inverse

lemma; [source line 126](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:126)

```lean
lemma fixedCount_inverse {n : ℕ} (π : Equiv.Perm (Fin n)) :
    fixedCount π.symm = fixedCount π
```

### remaining_nonempty

lemma; [source line 130](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:130)

```lean
lemma remaining_nonempty {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (remaining π k).Nonempty
```

### predictableChance

def; [source line 134](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:134)

The explicit predictable probability in `eq:predictable-p`.

```lean
noncomputable def predictableChance {n : ℕ} (w : Weights n)
    (π : Equiv.Perm (Fin n)) (k : Fin n) : ℝ :=
  w.choice (remaining π k) k
```

### predictableChance_formula

lemma; [source line 138](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:138)

```lean
lemma predictableChance_formula {n : ℕ} (w : Weights n)
    (π : Equiv.Perm (Fin n)) (k : Fin n) :
    predictableChance w π k =
      (if k ≤ π.symm k then w.rate k else 0) / w.total (remaining π k)
```

### predictableChance_le_rate_div

lemma; [source line 144](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:144)

```lean
lemma predictableChance_le_rate_div {n : ℕ} (w : Weights n)
    (π : Equiv.Perm (Fin n)) (k : Fin n) :
    predictableChance w π k ≤ w.rate k / w.total (remaining π k)
```

### survivorSet

def; [source line 153](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:153)

The clocks that survive strictly beyond time `t`.

```lean
noncomputable def survivorSet {n : ℕ} (times : Fin n → ℝ) (t : ℝ) :
    Finset (Fin n) := Finset.univ.filter (fun i => t < times i)
```

### raceRank

def; [source line 157](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:157)

The one-based rank representation in `eq:rank-representation`.

```lean
noncomputable def raceRank {n : ℕ} (times : Fin n → ℝ) (i : Fin n) : ℕ :=
  1 + (Finset.univ.filter fun j => times j < times i).card
```

### raceRank_add_survivors

lemma; [source line 162](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:162)

For distinct clocks, arrivals before `i`, survivors after `i`, and `i`
partition the labels.

```lean
lemma raceRank_add_survivors {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) (i : Fin n) :
    raceRank times i + (survivorSet times (times i)).card = n
```

### raceRank_eq_iff_survivors

lemma; [source line 190](D:/princeton/Research/Lean/Lean_luce/Luce/Section1Model.lean:190)

```lean
lemma raceRank_eq_iff_survivors {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) (i : Fin n) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    raceRank times i = k ↔ (survivorSet times (times i)).card = n - k
```


## Luce/Section2PointMeasureLaplace.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Topology
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction
namespace Luce
variable {X : Type*} [TopologicalSpace X]
section PointMeasures
variable [MeasurableSpace X] [OpensMeasurableSpace X]
```

### PointMomentSpace

abbrev; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:19)

```lean
abbrev PointMomentSpace (X : Type*) [TopologicalSpace X] :=
  WeakDual ℝ≥0 (X →ᵇ ℝ≥0)
```

### momentLaplace

def; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:24)

A bounded nonnegative spatial test gives a continuous Laplace coordinate
on the moment space.

```lean
noncomputable def momentLaplace (g : X →ᵇ ℝ≥0) : C(PointMomentSpace X, ℝ) :=
  ⟨fun u => Real.exp (-(u g : ℝ)),
    Real.continuous_exp.comp ((NNReal.continuous_coe.comp
      (WeakDual.eval_continuous g)).neg)⟩
```

### momentLaplace_apply

theorem; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:29)

```lean
@[simp] theorem momentLaplace_apply (g : X →ᵇ ℝ≥0) (u : PointMomentSpace X) :
    momentLaplace g u = Real.exp (-(u g : ℝ))
```

### momentLaplace_zero

theorem; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:32)

```lean
@[simp] theorem momentLaplace_zero : momentLaplace (0 : X →ᵇ ℝ≥0) = 1
```

### momentLaplace_add

theorem; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:36)

```lean
theorem momentLaplace_add (g h : X →ᵇ ℝ≥0) :
    momentLaplace (g + h) = momentLaplace g * momentLaplace h
```

### momentLaplaceMonoid

def; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:42)

Products of Laplace coordinates are again Laplace coordinates.

```lean
noncomputable def momentLaplaceMonoid : Submonoid C(PointMomentSpace X, ℝ) where
  carrier := Set.range momentLaplace
  one_mem' := ⟨0, momentLaplace_zero⟩
  mul_mem' := by
    rintro a b ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g + h, momentLaplace_add g h⟩
```

### momentLaplaceAlgebra

def; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:50)

The algebra generated by the Laplace coordinates.

```lean
noncomputable def momentLaplaceAlgebra : Subalgebra ℝ C(PointMomentSpace X, ℝ) :=
  Algebra.adjoin ℝ (momentLaplaceMonoid (X := X) : Set C(PointMomentSpace X, ℝ))
```

### momentLaplaceAlgebra_eq_span

theorem; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:53)

```lean
theorem momentLaplaceAlgebra_eq_span :
    (momentLaplaceAlgebra (X := X)).toSubmodule =
      Submodule.span ℝ (Set.range (momentLaplace (X := X)))
```

### momentLaplaceAlgebra_separatesPoints

theorem; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:59)

```lean
theorem momentLaplaceAlgebra_separatesPoints :
    (momentLaplaceAlgebra (X := X)).SeparatesPoints
```

### norm_momentLaplace_le_one

theorem; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:68)

```lean
theorem norm_momentLaplace_le_one (g : X →ᵇ ℝ≥0) (u : PointMomentSpace X) :
    ‖momentLaplace g u‖ ≤ 1
```

### momentLaplaceAlgebra_bounded

theorem; [source line 75](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:75)

Every Laplace polynomial is globally bounded, before restricting to
any compact set of point measures.

```lean
theorem momentLaplaceAlgebra_bounded (a : C(PointMomentSpace X, ℝ))
    (ha : a ∈ momentLaplaceAlgebra) :
    ∃ C : ℝ, ∀ u, ‖a u‖ ≤ C
```

### pointMoment

def; [source line 102](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:102)

The weak moment map on actual finite point measures.

```lean
noncomputable def pointMoment (μ : FinitePointMeasure X) : PointMomentSpace X :=
  FiniteMeasure.toWeakDualBCNN μ.toFiniteMeasure
```

### continuous_pointMoment

theorem; [source line 105](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:105)

```lean
theorem continuous_pointMoment : Continuous (pointMoment (X := X))
```

### isInducing_pointMoment

theorem; [source line 109](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:109)

```lean
theorem isInducing_pointMoment : IsInducing (pointMoment (X := X))
```

### measurable_momentLaplace_pointMoment

theorem; [source line 115](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:115)

```lean
theorem measurable_momentLaplace_pointMoment (g : X →ᵇ ℝ≥0) :
    Measurable (fun μ : FinitePointMeasure X => momentLaplace g (pointMoment μ))
```

### measurable_momentLaplaceAlgebra_pointMoment

theorem; [source line 123](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:123)

```lean
theorem measurable_momentLaplaceAlgebra_pointMoment (a : C(PointMomentSpace X, ℝ))
    (ha : a ∈ momentLaplaceAlgebra) :
    Measurable (fun μ : FinitePointMeasure X => a (pointMoment μ))
```

### momentLaplace_pointMoment_eq_pointLaplace

theorem; [source line 138](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLaplace.lean:138)

```lean
theorem momentLaplace_pointMoment_eq_pointLaplace (g : X →ᵇ ℝ≥0)
    (μ : FinitePointMeasure X) :
    momentLaplace g (pointMoment μ) = pointLaplace (fun x => (g x : ℝ)) μ
```


## Luce/Section2PointMeasureLawConvergence.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLawConvergence.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal
namespace Luce
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
```

### measurable_pointMeasure_mass

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLawConvergence.lean:21)

```lean
theorem measurable_pointMeasure_mass :
    Measurable (fun s : FinitePointMeasure X => s.toFiniteMeasure.mass)
```

### pointMeasure_eventually_mass_le

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLawConvergence.lean:27)

```lean
theorem pointMeasure_eventually_mass_le (s : FinitePointMeasure X) :
    ∀ᶠ N : ℕ in atTop, s.toFiniteMeasure.mass ≤ N
```

### measurable_boundedContinuous_pointMeasure

theorem; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLawConvergence.lean:40)

Every bounded weak-continuous real test is evaluation measurable on the
space of finite point measures, including for arbitrary compact spaces.

```lean
theorem measurable_boundedContinuous_pointMeasure [CompactSpace X]
    (F : FinitePointMeasure X →ᵇ ℝ) : Measurable F
```

### pointMeasure_mass_tail_tendsto_zero

theorem; [source line 51](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLawConvergence.lean:51)

The total-mass tails of any finite law on finite point measures tend to
zero. No expected-mass or regularity hypothesis on the law is needed.

```lean
theorem pointMeasure_mass_tail_tendsto_zero
    (Q : Measure (FinitePointMeasure X)) [IsFiniteMeasure Q] :
    Tendsto (fun N : ℕ => Q.real {s | (N : ℝ≥0) < s.toFiniteMeasure.mass})
      atTop (𝓝 0)
```

### integrable_momentLaplaceAlgebra_pointMoment

theorem; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLawConvergence.lean:73)

```lean
theorem integrable_momentLaplaceAlgebra_pointMoment
    (Q : Measure (FinitePointMeasure X)) [IsFiniteMeasure Q]
    (a : C(PointMomentSpace X, ℝ)) (ha : a ∈ momentLaplaceAlgebra) :
    Integrable (fun s => a (pointMoment s)) Q
```

### tendsto_integral_momentLaplaceAlgebra

theorem; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLawConvergence.lean:84)

Products of Laplace coordinates are again coordinates, so convergence
extends to their entire algebra by linearity of the integral.

```lean
theorem tendsto_integral_momentLaplaceAlgebra
    (μ : ℕ → Measure (FinitePointMeasure X)) (Q : Measure (FinitePointMeasure X))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure Q]
    (hLaplace : ∀ g : X →ᵇ ℝ≥0,
      Tendsto (fun n => ∫ s, momentLaplace g (pointMoment s) ∂μ n)
        atTop (𝓝 (∫ s, momentLaplace g (pointMoment s) ∂Q)))
    (a : C(PointMomentSpace X, ℝ)) (ha : a ∈ momentLaplaceAlgebra) :
    Tendsto (fun n => ∫ s, a (pointMoment s) ∂μ n)
      atTop (𝓝 (∫ s, a (pointMoment s) ∂Q))
```

### pointMeasure_law_convergence_of_laplace

theorem; [source line 120](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PointMeasureLawConvergence.lean:120)

Laplace convergence plus eventual tightness of total counts yields the
full bounded-continuous-test conclusion for laws of finite point measures.

```lean
theorem pointMeasure_law_convergence_of_laplace [CompactSpace X]
    (μ : ℕ → Measure (FinitePointMeasure X)) (Q : Measure (FinitePointMeasure X))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure Q]
    (hLaplace : ∀ g : X →ᵇ ℝ≥0,
      Tendsto (fun n => ∫ s, momentLaplace g (pointMoment s) ∂μ n)
        atTop (𝓝 (∫ s, momentLaplace g (pointMoment s) ∂Q)))
    (hTight : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ n in atTop,
      (μ n).real {s | (N : ℝ≥0) < s.toFiniteMeasure.mass} < ε)
    (F : FinitePointMeasure X →ᵇ ℝ) :
    Tendsto (fun n => ∫ s, F s ∂μ n) atTop (𝓝 (∫ s, F s ∂Q))
```


## Luce/Section2PoissonCriterion.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PoissonCriterion.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter Topology
open scoped NNReal BoundedContinuousFunction BigOperators
namespace Luce
```

### predictable_poisson

theorem; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PoissonCriterion.lean:25)

The full finite-row predictable Poisson random-measure criterion.
No independence between observations, deterministic probability caps,
or spatial separation/countability assumptions are imposed.

```lean
theorem predictable_poisson
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (B : ∀ n, FiniteAdaptedBernoulli (P n) n)
    (x : ∀ n, Fin n → X) (ν : FiniteMeasure X)
    (hweak : WeakMeasureConvergesInProbability P
      (fun n => (B n).predictableMeasure (x n)) ν)
    (hmax : ConvergesInProbability P
      (fun n => (B n).toProcess.rowMaximum n) 0)
    (F : FinitePointMeasure X →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F ((B n).pointMeasure (x n) ω) ∂P n)
      atTop (𝓝 (∫ μ, F μ ∂finitePoissonLaw ν))
```


## Luce/Section2PoissonMixture.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PoissonMixture.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Nat
namespace Luce
```

### poissonMixture

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PoissonMixture.lean:20)

A probability mixture whose component index has the scalar Poisson law.

```lean
noncomputable def poissonMixture {E : Type*} [MeasurableSpace E]
    (r : ℝ≥0) (Q : ℕ → Measure E) : Measure E :=
  (poissonMeasure r).bind Q
```

### instance at line 24

instance; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PoissonMixture.lean:24)

```lean
instance poissonMixture_isProbabilityMeasure {E : Type*} [MeasurableSpace E]
    (r : ℝ≥0) (Q : ℕ → Measure E) [∀ m, IsProbabilityMeasure (Q m)] :
    IsProbabilityMeasure (poissonMixture r Q) :=
  isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
    (Eventually.of_forall fun _ => inferInstance)
```

### integrable_of_zero_le_le_one

lemma; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PoissonMixture.lean:30)

```lean
private lemma integrable_of_zero_le_le_one {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (F : E → ℝ)
    (hF : Measurable F) (hF01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    Integrable F μ
```

### integral_pow_poissonMeasure

theorem; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PoissonMixture.lean:41)

The scalar Poisson probability-generating function on `[0,1]`, including
zero rate and zero argument. Integrability is established before using the
Poisson-series integral formula.

```lean
theorem integral_pow_poissonMeasure (r : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ m : ℕ, a ^ m ∂poissonMeasure r) = Real.exp (-(r : ℝ) * (1 - a))
```

### integrable_poissonMixture

theorem; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PoissonMixture.lean:64)

A bounded measurable test is integrable under the Poisson mixture.

```lean
theorem integrable_poissonMixture {E : Type*} [MeasurableSpace E]
    (r : ℝ≥0) (Q : ℕ → Measure E) [∀ m, IsProbabilityMeasure (Q m)]
    (F : E → ℝ) (hF : Measurable F) (hF01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    Integrable F (poissonMixture r Q)
```

### integral_poissonMixture_of_power

theorem; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PoissonMixture.lean:73)

If the test integral in the component with `m` points is `a ^ m`,
mixing those components with a Poisson count gives the required exponential
formula. No nonempty state-space or positive-rate hypothesis is imposed.

```lean
theorem integral_poissonMixture_of_power {E : Type*} [MeasurableSpace E]
    (r : ℝ≥0) (Q : ℕ → Measure E) [∀ m, IsProbabilityMeasure (Q m)]
    (F : E → ℝ) (hF : Measurable F) (hF01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomponent : ∀ m : ℕ, (∫ x, F x ∂Q m) = a ^ m) :
    (∫ x, F x ∂poissonMixture r Q) = Real.exp (-(r : ℝ) * (1 - a))
```


## Luce/Section2Predictable.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Luce
section Conditional
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
```

### exp_neg_mul_of_zero_one

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:19)

The Laplace transform of a zero-one variable is affine in that variable.

```lean
theorem exp_neg_mul_of_zero_one {b g : ℝ} (hb : b = 0 ∨ b = 1) :
    Real.exp (-g * b) = 1 - (1 - Real.exp (-g)) * b
```

### bernoulli_likelihood_mean

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:24)

The normalized Bernoulli likelihood has mean one.

```lean
theorem bernoulli_likelihood_mean {p q : ℝ} (hd : 1 - p * q ≠ 0) :
    (1 - p) * (1 / (1 - p * q)) + p * ((1 - q) / (1 - p * q)) = 1
```

### bernoulli_likelihood_second_moment

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:30)

The exact second moment used in the stopped likelihood estimate.

```lean
theorem bernoulli_likelihood_second_moment {p q : ℝ} (hd : 1 - p * q ≠ 0) :
    (1 - p) * (1 / (1 - p * q)) ^ 2 + p * ((1 - q) / (1 - p * q)) ^ 2 =
      1 + p * (1 - p) * q ^ 2 / (1 - p * q) ^ 2
```

### likelihood_denominator_pos

theorem; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:37)

Stopping at `p ≤ δ < 1` keeps every likelihood denominator positive.

```lean
theorem likelihood_denominator_pos {p q δ : ℝ} (hp : 0 ≤ p) (hpδ : p ≤ δ)
    (hδ : δ < 1) (hq : q ≤ 1) : 0 < 1 - p * q
```

### bernoulli_likelihood_second_moment_le

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:43)

A uniform exponential bound for the second moment of a stopped factor.

```lean
theorem bernoulli_likelihood_second_moment_le {p q δ : ℝ}
    (hp : 0 ≤ p) (hpδ : p ≤ δ) (hδ : δ < 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - p) * (1 / (1 - p * q)) ^ 2 + p * ((1 - q) / (1 - p * q)) ^ 2 ≤
      Real.exp (p / (1 - δ) ^ 2)
```

### condExp_bernoulli_laplace

theorem; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:72)

Conditional Laplace transform identity for an adapted Bernoulli variable.

```lean
theorem condExp_bernoulli_laplace (hm : m ≤ mΩ) {I p : Ω → ℝ}
    (hI : Integrable I μ) (hIp : μ[I | m] =ᵐ[μ] p)
    (h01 : ∀ᵐ ω ∂μ, I ω = 0 ∨ I ω = 1) (g : ℝ) :
    μ[(fun ω => Real.exp (-g * I ω)) | m] =ᵐ[μ]
      (fun ω => 1 - (1 - Real.exp (-g)) * p ω)
```

### condExp_normalized_bernoulli

theorem; [source line 90](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:90)

Dividing the conditional Laplace transform by its predictable mean
produces a conditionally mean-one factor.

```lean
theorem condExp_normalized_bernoulli (hm : m ≤ mΩ) {I p : Ω → ℝ}
    (hI : Integrable I μ) (hIp : μ[I | m] =ᵐ[μ] p)
    (h01 : ∀ᵐ ω ∂μ, I ω = 0 ∨ I ω = 1) (hp : StronglyMeasurable[m] p)
    (g : ℝ) (hd : ∀ᵐ ω ∂μ, 1 - p ω * (1 - Real.exp (-g)) ≠ 0)
    (hint : Integrable (fun ω => Real.exp (-g * I ω) /
      (1 - p ω * (1 - Real.exp (-g)))) μ) :
    μ[(fun ω => Real.exp (-g * I ω) / (1 - p ω * (1 - Real.exp (-g)))) | m]
      =ᵐ[μ] (fun _ => 1)
```

### likelihood_product_martingale

theorem; [source line 115](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:115)

Products of adapted, conditionally mean-one factors form a martingale.
Integrability is explicit; in the stopped construction it follows from the
positive lower bound on each denominator.

```lean
theorem likelihood_product_martingale (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k))
    (hYint : ∀ k, Integrable (Y k) μ)
    (hmean : ∀ k, μ[Y k | ℱ k] =ᵐ[μ] fun _ => 1)
    (hprod : ∀ k, Integrable (fun ω => ∏ j ∈ Finset.range k, Y j ω) μ) :
    Martingale (fun k ω => ∏ j ∈ Finset.range k, Y j ω) ℱ μ
```

### likelihood_product_integral

theorem; [source line 139](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:139)

Every finite likelihood product has expectation one.

```lean
theorem likelihood_product_integral (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k))
    (hYint : ∀ k, Integrable (Y k) μ)
    (hmean : ∀ k, μ[Y k | ℱ k] =ᵐ[μ] fun _ => 1)
    (hprod : ∀ k, Integrable (fun ω => ∏ j ∈ Finset.range k, Y j ω) μ) (k : ℕ) :
    (∫ ω, ∏ j ∈ Finset.range k, Y j ω ∂μ) = 1
```

### likelihood_integral_error

theorem; [source line 153](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:153)

A bounded mean-one likelihood transfers an `L¹` approximation to its
weighted expectation. This justifies the expectation passage in Section 2.

```lean
theorem likelihood_integral_error {L A : Ω → ℝ} {C c : ℝ}
    (hL : Integrable L μ) (hA : Integrable A μ)
    (hmean : (∫ ω, L ω ∂μ) = 1)
    (hL0 : ∀ᵐ ω ∂μ, 0 ≤ L ω) (hLC : ∀ᵐ ω ∂μ, L ω ≤ C) :
    |(∫ ω, L ω * A ω ∂μ) - c| ≤ C * ∫ ω, |A ω - c| ∂μ
```

### log_one_sub_remainder

theorem; [source line 182](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:182)

Explicit quadratic remainder in the logarithm expansion.

```lean
theorem log_one_sub_remainder {x δ : ℝ} (hx : 0 ≤ x) (hxδ : x ≤ δ)
    (hδ : δ < 1) : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - δ)
```

### log_product_remainder

theorem; [source line 194](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:194)

The logarithmic product error is controlled by the largest atom times
the total compensator. This is the deterministic expansion in Section 2.

```lean
theorem log_product_remainder {ι : Type*} (s : Finset ι) (x : ι → ℝ) {δ : ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (hxδ : ∀ i ∈ s, x i ≤ δ) (hδ : δ < 1) :
    |Real.log (∏ i ∈ s, (1 - x i)) + ∑ i ∈ s, x i| ≤
      δ * (∑ i ∈ s, x i) / (1 - δ)
```

### exp_sub_le_sub_of_nonpos

theorem; [source line 214](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:214)

Exponentiation on the negative half-line is one-Lipschitz.

```lean
theorem exp_sub_le_sub_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b|
```

### product_poisson_error

theorem; [source line 232](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:232)

Quantitative Poisson-product approximation for a finite array.

```lean
theorem product_poisson_error {ι : Type*} (s : Finset ι) (x : ι → ℝ) {δ lam : ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (hxδ : ∀ i ∈ s, x i ≤ δ)
    (hδ : δ < 1) (hlam : 0 ≤ lam) :
    |(∏ i ∈ s, (1 - x i)) - Real.exp (-lam)| ≤
      δ * (∑ i ∈ s, x i) / (1 - δ) + |(∑ i ∈ s, x i) - lam|
```

### inverse_product_le_exp

theorem; [source line 260](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:260)

A deterministic bound for the stopped likelihood, avoiding any independence
assumption and giving uniform integrability directly.

```lean
theorem inverse_product_le_exp {ι : Type*} (s : Finset ι) (x : ι → ℝ) {δ K : ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (hxδ : ∀ i ∈ s, x i ≤ δ)
    (hδ : δ < 1) (hsum : ∑ i ∈ s, x i ≤ K) :
    (∏ i ∈ s, (1 - x i))⁻¹ ≤ Real.exp (K / (1 - δ))
```

### product_poisson_error_of_atom_bound

theorem; [source line 278](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Predictable.lean:278)

A form of the product error separating a fixed denominator cap from a
possibly random upper bound on the largest atom.

```lean
theorem product_poisson_error_of_atom_bound {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {a δ K lam : ℝ} (hx : ∀ i ∈ s, 0 ≤ x i) (hxa : ∀ i ∈ s, x i ≤ a)
    (ha : 0 ≤ a) (haδ : a ≤ δ) (hδ : δ < 1)
    (hsum : ∑ i ∈ s, x i ≤ K) (hlam : 0 ≤ lam) :
    |(∏ i ∈ s, (1 - x i)) - Real.exp (-lam)| ≤
      K / (1 - δ) * a + |(∑ i ∈ s, x i) - lam|
```


## Luce/Section2PredictablePoisson.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PredictablePoisson.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
namespace BernoulliProcess
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
```

### capped_laplace_tendsto_rows

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PredictablePoisson.lean:21)

The capped Laplace criterion on the natural varying row spaces.

```lean
theorem capped_laplace_tendsto_rows (X : ∀ n, BernoulliProcess (μ n))
    (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) {δ K lam : ℝ} (hδ : δ < 1) (hlam : 0 ≤ lam)
    (hg : ∀ n k, 0 ≤ g n k) (a : ∀ n, Ω n → ℝ)
    (hameas : ∀ n, Measurable (a n)) (ha0 : ∀ n ω, 0 ≤ a n ω)
    (haδ : ∀ n ω, a n ω ≤ δ)
    (hp : ∀ n k ω, (X n).probability k ω ≤ a n ω)
    (hK : ∀ n ω, ∑ k ∈ Finset.range (N n), (X n).probability k ω ≤ K)
    (hatendsto : ConvergesInProbability μ a 0)
    (hcomp : ConvergesInProbability μ
      (fun n => (X n).laplaceCompensator (g n) (N n)) lam) :
    Tendsto (fun n => ∫ ω, Real.exp (-(∑ k ∈ Finset.range (N n),
      g n k * (X n).observation k ω)) ∂μ n) atTop (𝓝 (Real.exp (-lam)))
```


## Luce/Section2PredictableProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PredictableProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
open scoped BigOperators
universe u
namespace Luce
```

### predictable_fixed_point_probability

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section2PredictableProbability.lean:20)

The exact approved arbitrary-space conditional expectation identity.

```lean
theorem predictable_fixed_point_probability
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ)
    (k : Fin n) :
    P[(fun ω => if (π ω).symm k = k then (1 : ℝ) else 0)
        | drawHistory π k.val] =ᵐ[P]
      (fun ω =>
        (if k ≤ (π ω).symm k then w.rate k else 0) /
          w.total (remaining (π ω) k))
```


## Luce/Section2ProbabilityConvergence.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ProbabilityConvergence.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped Topology
namespace Luce
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
```

### tendsto_integral_abs_of_bounded_inMeasure

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ProbabilityConvergence.lean:21)

Uniformly bounded random variables converging in probability to a constant
converge in `L¹` to that constant.

```lean
theorem tendsto_integral_abs_of_bounded_inMeasure {A : ℕ → Ω → ℝ} {c B : ℝ}
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, |A n ω| ≤ B)
    (hconv : TendstoInMeasure μ A atTop (fun _ => c)) :
    Tendsto (fun n => ∫ ω, |A n ω - c| ∂μ) atTop (𝓝 0)
```

### tendsto_likelihood_integral

theorem; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ProbabilityConvergence.lean:45)

A sequence of bounded mean-one likelihoods may multiply the preceding
convergence even when each likelihood depends on the random variable.

```lean
theorem tendsto_likelihood_integral {L A : ℕ → Ω → ℝ} {c B C : ℝ}
    (hL : ∀ n, Integrable (L n) μ) (hA : ∀ n, Integrable (A n) μ)
    (hmean : ∀ n, (∫ ω, L n ω ∂μ) = 1)
    (hL0 : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ L n ω)
    (hLC : ∀ n, ∀ᵐ ω ∂μ, L n ω ≤ C)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, |A n ω| ≤ B)
    (hconv : TendstoInMeasure μ A atTop (fun _ => c)) :
    Tendsto (fun n => ∫ ω, L n ω * A n ω ∂μ) atTop (𝓝 c)
```

### integral_abs_le_threshold_add_probability

theorem; [source line 71](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ProbabilityConvergence.lean:71)

The elementary bounded-convergence estimate, also valid when the
probability space changes from one row to the next.

```lean
theorem integral_abs_le_threshold_add_probability {A : Ω → ℝ} {c B ε : ℝ}
    (hA : Measurable A) (hbound : ∀ ω, |A ω - c| ≤ B) (hε : 0 ≤ ε) :
    (∫ ω, |A ω - c| ∂μ) ≤ ε + B * μ.real {ω | ε < |A ω - c|}
```

### tendsto_integral_abs_of_bounded_probability

theorem; [source line 100](D:/princeton/Research/Lean/Lean_luce/Luce/Section2ProbabilityConvergence.lean:100)

Bounded convergence in probability for triangular arrays on different
probability spaces, in the real-valued tail-probability formulation.

```lean
theorem tendsto_integral_abs_of_bounded_probability
    {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)] (μ' : ∀ n, Measure (Ω' n))
    [∀ n, IsProbabilityMeasure (μ' n)] (A : ∀ n, Ω' n → ℝ) {c B : ℝ}
    (hA : ∀ n, Measurable (A n)) (hbound : ∀ n ω, |A n ω - c| ≤ B)
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ' n).real {ω | ε < |A n ω - c|}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |A n ω - c| ∂μ' n) atTop (𝓝 0)
```


## Luce/Section3ProfileKernels.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Luce
section Integrals
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
```

### survivalKernel

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:22)

```lean
def survivalKernel (t a : ℝ) : ℝ := Real.exp (-t * a)
```

### rateKernel

def; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:24)

```lean
def rateKernel (t a : ℝ) : ℝ := a * survivalKernel t a
```

### survivalKernel_pos

lemma; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:26)

```lean
lemma survivalKernel_pos (t a : ℝ) : 0 < survivalKernel t a
```

### survivalKernel_le_one

lemma; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:28)

```lean
lemma survivalKernel_le_one {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) :
    survivalKernel t a ≤ 1
```

### rateKernel_nonneg

lemma; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:33)

```lean
lemma rateKernel_nonneg {t a : ℝ} (ha : 0 ≤ a) : 0 ≤ rateKernel t a
```

### rateKernel_le

lemma; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:36)

```lean
lemma rateKernel_le {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) : rateKernel t a ≤ a
```

### survivalKernel_antitone_time

lemma; [source line 39](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:39)

```lean
lemma survivalKernel_antitone_time {a : ℝ} (ha : 0 ≤ a) :
    Antitone (fun t => survivalKernel t a)
```

### rateKernel_antitone_time

lemma; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:45)

```lean
lemma rateKernel_antitone_time {a : ℝ} (ha : 0 ≤ a) :
    Antitone (fun t => rateKernel t a)
```

### hasDerivAt_survivalKernel

lemma; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:50)

```lean
lemma hasDerivAt_survivalKernel (t a : ℝ) :
    HasDerivAt (survivalKernel t) (-t * survivalKernel t a) a
```

### hasDerivAt_rateKernel

lemma; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:55)

```lean
lemma hasDerivAt_rateKernel (t a : ℝ) :
    HasDerivAt (rateKernel t) ((1 - t * a) * survivalKernel t a) a
```

### abs_rateKernel_derivative_le_one

lemma; [source line 63](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:63)

```lean
lemma abs_rateKernel_derivative_le_one {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) :
    |(1 - t * a) * survivalKernel t a| ≤ 1
```

### abs_rateKernel_sub_le

theorem; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:76)

```lean
theorem abs_rateKernel_sub_le {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |rateKernel t a - rateKernel t b| ≤ |a - b|
```

### abs_survivalKernel_sub_le

theorem; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:84)

```lean
theorem abs_survivalKernel_sub_le {t a b : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |survivalKernel t a - survivalKernel t b| ≤ t * |a - b|
```

### profileH

def; [source line 99](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:99)

```lean
def profileH (μ : Measure Ω) (f : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ x, survivalKernel t (f x) ∂μ
```

### profileF

def; [source line 102](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:102)

```lean
def profileF (μ : Measure Ω) (f : Ω → ℝ) (t : ℝ) : ℝ := 1 - profileH μ f t
```

### profileD

def; [source line 104](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:104)

```lean
def profileD (μ : Measure Ω) (f : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ x, rateKernel t (f x) ∂μ
```

### integrable_rateKernel

lemma; [source line 107](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:107)

```lean
lemma integrable_rateKernel {f : Ω → ℝ} (hf : Integrable f μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => rateKernel t (f x)) μ
```

### integrable_survivalKernel

lemma; [source line 118](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:118)

```lean
lemma integrable_survivalKernel [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun x => survivalKernel t (f x)) μ
```

### abs_profileD_sub_le

theorem; [source line 128](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:128)

L¹ stability of the remaining-rate transform, uniformly for every nonnegative time.

```lean
theorem abs_profileD_sub_le {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) (hg₀ : ∀ᵐ x ∂μ, 0 ≤ g x) {t : ℝ} (ht : 0 ≤ t) :
    |profileD μ f t - profileD μ g t| ≤ ∫ x, |f x - g x| ∂μ
```

### abs_profileF_sub_le

theorem; [source line 139](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:139)

L¹ stability of the arrival transform on a bounded time interval.

```lean
theorem abs_profileF_sub_le [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) (hg₀ : ∀ᵐ x ∂μ, 0 ≤ g x)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    |profileF μ f t - profileF μ g t| ≤ T * ∫ x, |f x - g x| ∂μ
```

### tendstoUniformlyOn_profileD

theorem; [source line 162](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:162)

L¹ convergence implies uniform convergence of the deterministic remaining rate,
even on the entire nonnegative time axis.

```lean
theorem tendstoUniformlyOn_profileD {f : Ω → ℝ} {fn : ℕ → Ω → ℝ}
    (hf : Integrable f μ) (hfn : ∀ n, Integrable (fn n) μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) (hfn₀ : ∀ n, ∀ᵐ x ∂μ, 0 ≤ fn n x)
    (hL₁ : Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => profileD μ (fn n)) (profileD μ f) atTop (Ici 0)
```

### tendstoUniformlyOn_profileF

theorem; [source line 174](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:174)

The arrival transforms converge uniformly on every bounded time interval.

```lean
theorem tendstoUniformlyOn_profileF [IsFiniteMeasure μ] {f : Ω → ℝ} {fn : ℕ → Ω → ℝ}
    (hf : Integrable f μ) (hfn : ∀ n, Integrable (fn n) μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) (hfn₀ : ∀ n, ∀ᵐ x ∂μ, 0 ≤ fn n x)
    (hL₁ : Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0)) (T : ℝ) :
    TendstoUniformlyOn (fun n => profileF μ (fn n)) (profileF μ f) atTop (Icc 0 T)
```

### tendsto_setIntegral_of_L1_of_measure_tendsto_zero

theorem; [source line 190](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:190)

The mass of any shrinking cells vanishes under L¹-convergent profiles.
Choosing the cell containing a largest weight is the maximum-weight argument
in equation `eq:max-weight`; no fixed choice of cells is required.

```lean
theorem tendsto_setIntegral_of_L1_of_measure_tendsto_zero
    {f : Ω → ℝ} {fn : ℕ → Ω → ℝ} {cells : ℕ → Set Ω}
    (hf : Integrable f μ) (hfn : ∀ n, Integrable (fn n) μ)
    (hL₁ : Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0))
    (hcells : Tendsto (fun n => μ (cells n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in cells n, fn n x ∂μ) atTop (𝓝 0)
```

### tendsto_normalized_weight_of_cells

theorem; [source line 207](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileKernels.lean:207)

A normalized weight represented as the mass of a shrinking profile cell is negligible.

```lean
theorem tendsto_normalized_weight_of_cells
    {f : Ω → ℝ} {fn : ℕ → Ω → ℝ} {cells : ℕ → Set Ω} {weights : ℕ → ℝ}
    (hf : Integrable f μ) (hfn : ∀ n, Integrable (fn n) μ)
    (hL₁ : Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0))
    (hcells : Tendsto (fun n => μ (cells n)) atTop (𝓝 0))
    (hweights : ∀ n, weights n / (n + 1 : ℕ) = ∫ x in cells n, fn n x ∂μ) :
    Tendsto (fun n => weights n / (n + 1 : ℕ)) atTop (𝓝 0)
```


## Luce/Section3ProfileRegularity.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileRegularity.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Luce
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
```

### continuousOn_profileD

theorem; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileRegularity.lean:13)

```lean
theorem continuousOn_profileD {f : Ω → ℝ} (hf : Integrable f μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) : ContinuousOn (profileD μ f) (Ici 0)
```

### continuousOn_profileH

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileRegularity.lean:27)

```lean
theorem continuousOn_profileH [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ContinuousOn (profileH μ f) (Ici 0)
```

### continuousOn_profileF

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileRegularity.lean:43)

```lean
theorem continuousOn_profileF [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ContinuousOn (profileF μ f) (Ici 0)
```

### antitoneOn_profileD

theorem; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileRegularity.lean:48)

```lean
theorem antitoneOn_profileD {f : Ω → ℝ} (hf : Integrable f μ)
    (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) : AntitoneOn (profileD μ f) (Ici 0)
```

### monotoneOn_profileF

theorem; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section3ProfileRegularity.lean:55)

```lean
theorem monotoneOn_profileF [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) :
    MonotoneOn (profileF μ f) (Ici 0)
```


## Luce/Section3RaceConvergence.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceConvergence.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
section Probability
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
```

### exists_finite_oscillation_grid

theorem; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceConvergence.lean:22)

A continuous function on a compact time interval admits a finite grid
whose bracketing values have arbitrarily small oscillation.

```lean
theorem exists_finite_oscillation_grid {f : ℝ → ℝ} {T δ : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hδ : 0 < δ) :
    ∃ grid : Finset ℝ, (∀ t ∈ grid, t ∈ Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, ∃ a ∈ grid, ∃ b ∈ grid,
        a ≤ t ∧ t ≤ b ∧ |f t - f a| ≤ δ ∧ |f b - f t| ≤ δ
```

### monotone_uniform_convergence_in_probability

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceConvergence.lean:81)

Pointwise convergence in probability of monotone sample paths to a
continuous limit is uniform on compact time intervals.

```lean
theorem monotone_uniform_convergence_in_probability
    {X : ∀ n, Ω n → ℝ → ℝ} {f : ℝ → ℝ} {T : ℝ}
    (hmono : ∀ n ω, Monotone (X n ω)) (hf : ContinuousOn f (Icc 0 T))
    (hpoint : ∀ t ∈ Icc 0 T, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |X n ω t - f t|}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => μ n {ω | ∃ t ∈ Icc 0 T, ε ≤ |X n ω t - f t|}) atTop (𝓝 0)
```

### antitone_uniform_convergence_in_probability

theorem; [source line 117](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceConvergence.lean:117)

The remaining-rate version of the uniform race theorem.

```lean
theorem antitone_uniform_convergence_in_probability
    {X : ∀ n, Ω n → ℝ → ℝ} {f : ℝ → ℝ} {T : ℝ}
    (hmono : ∀ n ω, Antitone (X n ω)) (hf : ContinuousOn f (Icc 0 T))
    (hpoint : ∀ t ∈ Icc 0 T, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |X n ω t - f t|}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => μ n {ω | ∃ t ∈ Icc 0 T, ε ≤ |X n ω t - f t|}) atTop (𝓝 0)
```

### concentration_of_variance_tendsto_zero

theorem; [source line 132](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceConvergence.lean:132)

Vanishing variance and convergent expectations imply convergence in
probability to a deterministic value, by Chebyshev's inequality.

```lean
theorem concentration_of_variance_tendsto_zero [∀ n, IsFiniteMeasure (μ n)]
    {X : ∀ n, Ω n → ℝ} {c : ℝ} (hX : ∀ n, MemLp (X n) 2 (μ n))
    (hvar : Tendsto (fun n => variance (X n) (μ n)) atTop (𝓝 0))
    (hmean : Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |X n ω - c|}) atTop (𝓝 0)
```


## Luce/Section1RaceOrder.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean)

Namespace / shared context (consult source for section boundaries):

```lean
namespace Luce
```

### beforeCount_lt

lemma; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:9)

The number of clocks strictly earlier than a fixed clock is less than `n`.

```lean
lemma beforeCount_lt {n : ℕ} (times : Fin n → ℝ) (i : Fin n) :
    (Finset.univ.filter fun j => times j < times i).card < n
```

### raceRank_strict

lemma; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:20)

Strictly earlier clocks have strictly smaller race ranks.

```lean
lemma raceRank_strict {n : ℕ} (times : Fin n → ℝ) {i j : Fin n}
    (hij : times i < times j) : raceRank times i < raceRank times j
```

### raceRank_injective

lemma; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:37)

```lean
lemma raceRank_injective {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) : Function.Injective (raceRank times)
```

### clockRank

def; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:50)

Zero-based rank as a valid position.

```lean
noncomputable def clockRank {n : ℕ} (times : Fin n → ℝ) (i : Fin n) : Fin n :=
  ⟨(Finset.univ.filter fun j => times j < times i).card, beforeCount_lt times i⟩
```

### clockRank_injective

lemma; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:53)

```lean
lemma clockRank_injective {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) : Function.Injective (clockRank times)
```

### rankPermutation

def; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:61)

The bijective rank map of a family of distinct clocks.

```lean
noncomputable def rankPermutation {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (clockRank times)
    ⟨clockRank_injective times hinj, Finite.surjective_of_injective (clockRank_injective times hinj)⟩
```

### drawPermutation

def; [source line 67](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:67)

The draw order is the inverse of the rank permutation.

```lean
noncomputable def drawPermutation {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) : Equiv.Perm (Fin n) :=
  (rankPermutation times hinj).symm
```

### arrivalTime

def; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:72)

The `k`th arrival time, with positions represented by `Fin n`.

```lean
noncomputable def arrivalTime {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) (k : Fin n) : ℝ :=
  times (drawPermutation times hinj k)
```

### clockRank_le_iff

lemma; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:76)

```lean
lemma clockRank_le_iff {n : ℕ} (times : Fin n → ℝ) (i j : Fin n) :
    clockRank times i ≤ clockRank times j ↔ times i ≤ times j
```

### rank_survives_iff

lemma; [source line 93](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:93)

Equation `eq:survival-indicator`: rank survival equals clock survival.

```lean
lemma rank_survives_iff {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) (i k : Fin n) :
    k ≤ rankPermutation times hinj i ↔ arrivalTime times hinj k ≤ times i
```

### remaining_eq_clock_survivors

lemma; [source line 103](D:/princeton/Research/Lean/Lean_luce/Luce/Section1RaceOrder.lean:103)

Equation `eq:remaining-weight`, evaluated at an arrival time.

```lean
lemma remaining_eq_clock_survivors {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) (k : Fin n) :
    remaining (drawPermutation times hinj) k =
      Finset.univ.filter fun i => arrivalTime times hinj k ≤ times i
```


## Luce/Section4RankIntegral.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankIntegral.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set
namespace Luce
```

### backgroundSurvivors_eq_erase

lemma; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankIntegral.lean:15)

Counting background survivors is equivalent to erasing the candidate from
one common full-clock survivor set.

```lean
lemma backgroundSurvivors_eq_erase {n : ℕ} (clocks : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) :
    backgroundSurvivors t (fun j => clocks (i.succAbove j)) =
      ((survivorSet clocks t).erase i).card
```

### exponentialRace_background

lemma; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankIntegral.lean:32)

```lean
lemma exponentialRace_background {n : ℕ} (w : Weights (n + 1)) (i : Fin (n + 1)) :
    MeasurePreserving (fun clocks : Fin (n + 1) → ℝ => fun j => clocks (i.succAbove j))
      (exponentialRace w) (backgroundRace w i)
```

### background_probability_eq_common

lemma; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankIntegral.lean:42)

The probability used in the rank integral can be evaluated in the common
full race, which permits the deterministic two-candidate estimate.

```lean
lemma background_probability_eq_common {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (t : ℝ) (m : ℕ) :
    backgroundRace w i {background | backgroundSurvivors t background = m} =
      exponentialRace w {clocks | ((survivorSet clocks t).erase i).card = m}
```

### rank_integral_real

theorem; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankIntegral.lean:54)

The exact rank integral as an ordinary real-valued integral. The density
`exponentialPDFReal` vanishes at all negative times.

```lean
theorem rank_integral_real {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (m : ℕ) :
    (exponentialRace w).real {clocks |
      backgroundSurvivors (clocks i) (fun j => clocks (i.succAbove j)) = m} =
      ∫ t, exponentialPDFReal (w.rate i) t *
        (backgroundRace w i).real {background | backgroundSurvivors t background = m}
```

### rank_integral_common

theorem; [source line 86](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankIntegral.lean:86)

The real rank integral evaluated entirely on one common exponential race.

```lean
theorem rank_integral_common {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (m : ℕ) :
    (exponentialRace w).real {clocks |
      ((survivorSet clocks (clocks i)).erase i).card = m} =
      ∫ t, exponentialPDFReal (w.rate i) t *
        (exponentialRace w).real {clocks | ((survivorSet clocks t).erase i).card = m}
```


## Luce/Section4RankIntegralDependencyAudit.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankIntegralDependencyAudit.lean)

No declarations; imports or audit commands only.


## Luce/Section4RankProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Set
namespace Luce
```

### exponentialPDFReal_eq_piecewise

lemma; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankProbability.lean:11)

```lean
lemma exponentialPDFReal_eq_piecewise (r t : ℝ) :
    exponentialPDFReal r t = if 0 ≤ t then r * Real.exp (-r * t) else 0
```

### integral_exponentialPDFReal

lemma; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankProbability.lean:17)

Restricting the density integral to positive times gives the familiar
exponential density.

```lean
lemma integral_exponentialPDFReal (r : ℝ) (P : ℝ → ℝ) :
    (∫ t, exponentialPDFReal r t * P t) =
      ∫ t in Ioi 0, r * Real.exp (-r * t) * P t
```

### raceRank_probability_integral

theorem; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankProbability.lean:31)

Conditioning on the distinguished exponential clock gives the exact
rank probability, for any requested one-based rank `r`.

```lean
theorem raceRank_probability_integral {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n + 1) :
    (exponentialRace w).real {clocks | raceRank clocks i = r} =
      ∫ t in Ioi 0, w.rate i * Real.exp (-w.rate i * t) *
        (exponentialRace w).real
          {clocks | ((survivorSet clocks t).erase i).card = n + 1 - r}
```

### fixed_point_probability_integral

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section4RankProbability.lean:56)

Equation `eq:rank-integral`, for the fixed-point event of label `i+1`.

```lean
theorem fixed_point_probability_integral {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) :
    (exponentialRace w).real {clocks | raceRank clocks i = i.val + 1} =
      ∫ t in Ioi 0, w.rate i * Real.exp (-w.rate i * t) *
        (exponentialRace w).real
          {clocks | ((survivorSet clocks t).erase i).card = n - i.val}
```


## Luce/Section3.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3.lean)

No declarations; imports or audit commands only.


## Luce/Section3Bernoulli.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Bernoulli.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace Luce
```

### raceDrawFiltration

def; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Bernoulli.lean:19)

The exact draw history, as a filtration on the exponential-clock space.

```lean
def raceDrawFiltration (n : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (Fin n → ℝ)) where
  seq := drawHistory raceDraw
  mono' := by
    intro a b hab
    unfold drawHistory
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    exact le_iSup_of_le j (le_iSup_of_le (lt_of_lt_of_le hj hab) le_rfl)
  le' := drawHistory_le raceDraw (measurable_raceDraw n)
```

### raceInteriorBernoulli

def; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Bernoulli.lean:33)

The fixed-point indicators restricted to the paper's interior window.
Spatial masking is deterministic, so the original draw history is retained.

```lean
def raceInteriorBernoulli {n : ℕ} (w : Weights n) (α : ℝ) :
    FiniteAdaptedBernoulli (exponentialRace w) n where
  filtration := raceDrawFiltration n
  observation k clocks := decide (((k.val : ℝ) + 1) / n ≤ α ∧ raceDraw clocks k = k)
  adapted k := by
    have htest : @Measurable (Fin n) Bool ⊤ inferInstance
        (fun i => decide (((k.val : ℝ) + 1) / n ≤ α ∧ i = k)) := fun _ _ => trivial
    exact htest.comp (measurable_draw_of_lt raceDraw k (Nat.lt_succ_self k.val))
```

### raceInteriorBernoulli_observation

theorem; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Bernoulli.lean:44)

The Bool representation is exactly the source's real indicator,
including the one-based coordinate and the inverse-permutation convention.

```lean
theorem raceInteriorBernoulli_observation {n : ℕ} (w : Weights n) (α : ℝ)
    (k : Fin n) (clocks : Fin n → ℝ) :
    (raceInteriorBernoulli w α).observationReal k clocks =
      if ((k.val : ℝ) + 1) / n ≤ α then
        (if (raceDraw clocks).symm k = k then 1 else 0) else 0
```

### raceInteriorBernoulli_probability

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Bernoulli.lean:56)

The exact conditional-probability identification required to invoke
the predictable Poisson criterion for the interior fixed-point process.

```lean
theorem raceInteriorBernoulli_probability {n : ℕ} (w : Weights n) (α : ℝ) (k : Fin n) :
    (raceInteriorBernoulli w α).probability k =ᵐ[exponentialRace w]
      (fun clocks => if ((k.val : ℝ) + 1) / n ≤ α then
        predictableChance w (raceDraw clocks) k else 0)
```


## Luce/Section3Compensator.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### survivalGe

def; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:19)

The paper's weak survival indicator, including equality at the threshold.

```lean
def survivalGe (t x : ℝ) : ℝ := if t ≤ x then 1 else 0
```

### measurable_survivalGe

lemma; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:21)

```lean
lemma measurable_survivalGe (t : ℝ) : Measurable (survivalGe t)
```

### survivalGe_mem_Icc

lemma; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:24)

```lean
lemma survivalGe_mem_Icc (t x : ℝ) : survivalGe t x ∈ Icc (0 : ℝ) 1
```

### survivalGe_sub_le_band

lemma; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:29)

The deterministic event containment in lines 763–765.

```lean
lemma survivalGe_sub_le_band {τ t x δ : ℝ} (hclose : |τ - t| ≤ δ) :
    |survivalGe τ x - survivalGe t x| ≤
      if |x - t| ≤ δ then 1 else 0
```

### rate_sq_survival_le

theorem; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:40)

An explicit version of `sup (a² exp(-a t)) < ∞`, with no bound on a.
Used for both the shrinking-band estimate and the interior variance.

```lean
theorem rate_sq_survival_le {r s u : ℝ} (hr : 0 ≤ r) (hu : 0 < u)
    (hus : u ≤ s) : r ^ 2 * survivalKernel s r ≤ 4 / u ^ 2
```

### hasDerivAt_rateKernel_time

lemma; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:60)

```lean
lemma hasDerivAt_rateKernel_time (r s : ℝ) :
    HasDerivAt (fun t => rateKernel t r) (-r ^ 2 * survivalKernel s r) s
```

### abs_rateKernel_time_sub_le

theorem; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:72)

Time-Lipschitz estimate away from zero, with a rate-independent constant.

```lean
theorem abs_rateKernel_time_sub_le {r s t u : ℝ} (hr : 0 ≤ r) (hu : 0 < u)
    (hus : u ≤ s) (hut : u ≤ t) :
    |rateKernel s r - rateKernel t r| ≤ (4 / u ^ 2) * |s - t|
```

### weighted_exponential_band_eq

lemma; [source line 85](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:85)

The weighted probability of a closed band is exactly a difference of
remaining-rate kernels. Atomlessness handles both band endpoints.

```lean
lemma weighted_exponential_band_eq {r t δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (ht : 0 ≤ t - δ) :
    r * (expMeasure r).real {x | |x - t| ≤ δ} =
      rateKernel (t - δ) r - rateKernel (t + δ) r
```

### weighted_exponential_band_le

theorem; [source line 109](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:109)

The explicit shrinking-band estimate in lines 767–772.

```lean
theorem weighted_exponential_band_le {r t δ u : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (hu : 0 < u) (hut : u ≤ t - δ) :
    r * (expMeasure r).real {x | |x - t| ≤ δ} ≤ 8 * δ / u ^ 2
```

### survival_replacement_bound

theorem; [source line 122](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:122)

Summing the pathwise replacement bound. In the paper `c i` is
`g(i/n)/D(t_i)` and `a i` is the rate; there is no restriction on dependence
between the perturbed times and the clocks.

```lean
theorem survival_replacement_bound {ι : Type*} (s : Finset ι)
    (a c τ t E : ι → ℝ) {δ C : ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hc : ∀ i ∈ s, |c i| ≤ C)
    (hclose : ∀ i ∈ s, |τ i - t i| ≤ δ) :
    |(∑ i ∈ s, c i * a i * survivalGe (τ i) (E i)) -
      (∑ i ∈ s, c i * a i * survivalGe (t i) (E i))| ≤
      C * ∑ i ∈ s, a i * (if |E i - t i| ≤ δ then 1 else 0)
```

### clockBand

def; [source line 145](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:145)

Closed-band indicator used only as a dominating random variable.

```lean
def clockBand (t δ x : ℝ) : ℝ := if |x - t| ≤ δ then 1 else 0
```

### measurable_clockBand

lemma; [source line 147](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:147)

```lean
lemma measurable_clockBand (t δ : ℝ) : Measurable (clockBand t δ)
```

### clockBand_mem_Icc

lemma; [source line 152](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:152)

```lean
lemma clockBand_mem_Icc (t δ x : ℝ) : clockBand t δ x ∈ Icc (0 : ℝ) 1
```

### integral_clockBand

lemma; [source line 156](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:156)

```lean
lemma integral_clockBand {r : ℝ} (_hr : 0 < r) (t δ : ℝ) :
    (∫ x, clockBand t δ x ∂expMeasure r) =
      (expMeasure r).real {x | |x - t| ≤ δ}
```

### integral_normalized_clockBand_le

theorem; [source line 169](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:169)

The integrated shrinking-band bound on the actual product law. The
constant is uniform over all rates, all labels, and all row sizes. This is
the expectation estimate to which the proof applies Markov's inequality.

```lean
theorem integral_normalized_clockBand_le {n : ℕ} (w : Weights (n + 1))
    (s : Finset (Fin (n + 1))) (t : Fin (n + 1) → ℝ) {δ u : ℝ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (ht : ∀ i ∈ s, u ≤ t i - δ) :
    (∫ E, (∑ i ∈ s, w.rate i * clockBand (t i) δ (E i)) / (n + 1 : ℕ)
      ∂exponentialRace w) ≤ 8 * δ / u ^ 2
```

### integral_survivalGe

lemma; [source line 199](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:199)

```lean
lemma integral_survivalGe {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    (∫ x, survivalGe t x ∂expMeasure r) = survivalKernel t r
```

### memLp_weighted_survivalGe

lemma; [source line 208](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:208)

```lean
lemma memLp_weighted_survivalGe {n : ℕ} (w : Weights n) (i : Fin n) (c t : ℝ) :
    MemLp (fun E : Fin n → ℝ => c * w.rate i * survivalGe t (E i)) 2
      (exponentialRace w)
```

### integral_normalized_survivalGe

theorem; [source line 218](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:218)

The exact expectation that remains after replacing the indicators,
as displayed in lines 787–793. The time may vary with the label.

```lean
theorem integral_normalized_survivalGe {n : ℕ} (w : Weights n)
    (s : Finset (Fin n)) (c t : Fin n → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) :
    (∫ E, (∑ i ∈ s, c i * w.rate i * survivalGe (t i) (E i)) / n
      ∂exponentialRace w) = (∑ i ∈ s, c i * rateKernel (t i) (w.rate i)) / n
```

### variance_weighted_survivalGe_le

lemma; [source line 234](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:234)

A single deterministic-time weighted survival variable has bounded
second moment after a positive time cutoff.

```lean
lemma variance_weighted_survivalGe_le {n : ℕ} (w : Weights n) (i : Fin n)
    {c t C u : ℝ} (hc : |c| ≤ C) (hu : 0 < u) (ht : u ≤ t) :
    variance (fun E : Fin n → ℝ => c * w.rate i * survivalGe t (E i))
      (exponentialRace w) ≤ 4 * C ^ 2 / u ^ 2
```

### variance_normalized_survivalGe_le

theorem; [source line 262](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Compensator.lean:262)

The independent-indicator variance step in lines 776–780. The finite
set s represents ηn < k ≤ αn; the product law supplies independence. Neither
bounded rates nor identically distributed clocks are assumed.

```lean
theorem variance_normalized_survivalGe_le {n : ℕ} (w : Weights (n + 1))
    (s : Finset (Fin (n + 1))) (c t : Fin (n + 1) → ℝ) {C u : ℝ}
    (hc : ∀ i ∈ s, |c i| ≤ C) (hu : 0 < u) (ht : ∀ i ∈ s, u ≤ t i) :
    variance (fun E =>
      (∑ i ∈ s, c i * w.rate i * survivalGe (t i) (E i)) / (n + 1 : ℕ))
      (exponentialRace w) ≤ (4 * C ^ 2 / u ^ 2) / (n + 1 : ℕ)
```


## Luce/Section3CompensatorLimit.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### profileDiagonal

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean:22)

The diagonal of the density in `eq:rho`. Its endpoint values are only
total extensions; all integrals in this section exclude zero and one.

```lean
def profileDiagonal (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  rateKernel (profileQuantile profileMeasure f x) (f x) /
    profileD profileMeasure f (profileQuantile profileMeasure f x)
```

### interiorCompensatorSum

def; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean:27)

The literal signed weighted sum in `eq:weighted-compensator`.

```lean
def interiorCompensatorSum {n : ℕ} (w : Weights n) (g : ℝ → ℝ)
    (α : ℝ) (E : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if ((i.val : ℝ) + 1) / n ≤ α then
    g (((i.val : ℝ) + 1) / n) * predictableChance w (raceDraw E) i else 0
```

### continuousOn_compensator_coefficient

lemma; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean:32)

```lean
lemma continuousOn_compensator_coefficient {w : WeightArray} {f g : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (hg : ContinuousOn g (Icc (0 : ℝ) α)) :
    ContinuousOn (fun x => g x / profileD profileMeasure f
      (profileQuantile profileMeasure f x)) (Icc (0 : ℝ) α)
```

### integrable_interior_density

theorem; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean:46)

The limiting integral exists as a genuine Bochner integral.

```lean
theorem integrable_interior_density {w : WeightArray} {f g : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (hg : ContinuousOn g (Icc (0 : ℝ) α)) :
    IntegrableOn (fun x => g x * profileDiagonal f x) (Ioc (0 : ℝ) α)
```

### section3_weighted_compensator

theorem; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean:64)

Proposition 3.2, equation `eq:weighted-compensator`, on the actual
exponential race. The next theorem transfers it to arbitrary row spaces.

```lean
theorem section3_weighted_compensator
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (0 : ℝ) α)) :
    ConvergesInProbability (fun n => exponentialRace (w (n + 1)))
      (fun n E => interiorCompensatorSum (w (n + 1)) g α E)
      (∫ x in Ioc (0 : ℝ) α, g x * profileDiagonal f x)
```

### section3_weighted_compensator_general

theorem; [source line 133](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean:133)

The weighted compensator limit on arbitrary row probability spaces,
with the original unshifted row index. Independence is only within rows.

```lean
theorem section3_weighted_compensator_general
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n))
    {α : ℝ} (hα : α < 1) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (0 : ℝ) α)) :
    ConvergesInProbability P
      (fun n ω => interiorCompensatorSum (w n) g α (fun i => E n i ω))
      (∫ x in Ioc (0 : ℝ) α, g x * profileDiagonal f x)
```

### intervalTestExtension

def; [source line 159](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean:159)

A continuous function whose domain is literally the paper's `[0,α]`
can be used without an extra extension hypothesis. Values outside are zero.

```lean
def intervalTestExtension (α : ℝ) (g : Icc (0 : ℝ) α → ℝ) (x : ℝ) : ℝ :=
  if hx : x ∈ Icc (0 : ℝ) α then g ⟨x, hx⟩ else 0
```

### intervalTestExtension_eq

lemma; [source line 162](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean:162)

```lean
lemma intervalTestExtension_eq (α : ℝ) (g : Icc (0 : ℝ) α → ℝ)
    (x : Icc (0 : ℝ) α) : intervalTestExtension α g x = g x
```

### continuousOn_intervalTestExtension

lemma; [source line 166](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean:166)

```lean
lemma continuousOn_intervalTestExtension (α : ℝ) (g : Icc (0 : ℝ) α → ℝ)
    (hg : Continuous g) : ContinuousOn (intervalTestExtension α g) (Icc (0 : ℝ) α)
```

### section3_weighted_compensator_on_interval

theorem; [source line 176](D:/princeton/Research/Lean/Lean_luce/Luce/Section3CompensatorLimit.lean:176)

Proposition 3.2 with a continuous test on exactly the source domain.
The extension is explicitly proved to agree on that domain above.

```lean
theorem section3_weighted_compensator_on_interval
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n))
    {α : ℝ} (hα : α < 1) (g : Icc (0 : ℝ) α → ℝ) (hg : Continuous g) :
    ConvergesInProbability P
      (fun n ω => interiorCompensatorSum (w n) (intervalTestExtension α g) α (fun i => E n i ω))
      (∫ x in Ioc (0 : ℝ) α, intervalTestExtension α g x * profileDiagonal f x)
```


## Luce/Section3Convergence.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Convergence.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter Set
open scoped Topology
namespace Luce.ConvergesInProbability
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X Y : ∀ n, Ω n → ℝ} {c d : ℝ}
```

### deterministic

theorem; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Convergence.lean:14)

```lean
theorem deterministic {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 c)) :
    ConvergesInProbability μ (fun n _ => a n) c
```

### add

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Convergence.lean:27)

```lean
theorem add (hX : ConvergesInProbability μ X c) (hY : ConvergesInProbability μ Y d) :
    ConvergesInProbability μ (fun n ω => X n ω + Y n ω) (c + d)
```

### neg

theorem; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Convergence.lean:48)

```lean
theorem neg (hX : ConvergesInProbability μ X c) :
    ConvergesInProbability μ (fun n ω => -X n ω) (-c)
```

### sub

theorem; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Convergence.lean:55)

```lean
theorem sub (hX : ConvergesInProbability μ X c) (hY : ConvergesInProbability μ Y d) :
    ConvergesInProbability μ (fun n ω => X n ω - Y n ω) (c - d)
```

### of_sub

theorem; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Convergence.lean:59)

```lean
theorem of_sub (hY : ConvergesInProbability μ Y c)
    (hXY : ConvergesInProbability μ (fun n ω => X n ω - Y n ω) 0) :
    ConvergesInProbability μ X c
```

### of_arbitrarily_close

theorem; [source line 67](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Convergence.lean:67)

Remove an initial block whose deterministic bound can be made
arbitrarily small, after sufficiently many rows. This is the double-limit
argument used three times in Proposition 3.2.

```lean
theorem of_arbitrarily_close
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ Y : ∀ n, Ω n → ℝ,
      ConvergesInProbability μ Y 0 ∧
        ∀ᶠ n in atTop, ∀ ω, |X n ω - Y n ω| ≤ ε) :
    ConvergesInProbability μ X 0
```


## Luce/Section3DenominatorReplacement.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3DenominatorReplacement.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace Luce
```

### race_probability_formula

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section3DenominatorReplacement.lean:17)

```lean
theorem race_probability_formula {n : ℕ} (w : Weights n)
    (E : Fin n → ℝ) (hinj : Function.Injective E) (k : Fin n) :
    predictableChance w (raceDraw E) k =
      w.rate k * survivalGe (orderTime E k) (E k) / w.total (remaining (raceDraw E) k)
```

### weighted_denominator_error_le

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section3DenominatorReplacement.lean:28)

Finite signed-coefficient version of the reciprocal-denominator bound.

```lean
theorem weighted_denominator_error_le {ι : Type*} (s : Finset ι)
    (a c W D : ι → ℝ) {d δ C : ℝ}
    (hd : 0 < d) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hmass : ∑ i ∈ s, a i ≤ 1)
    (hc : ∀ i ∈ s, |c i| ≤ C)
    (hW : ∀ i ∈ s, d ≤ W i) (hD : ∀ i ∈ s, d ≤ D i)
    (herr : ∀ i ∈ s, |W i - D i| ≤ δ) :
    |(∑ i ∈ s, c i * (a i / W i)) - (∑ i ∈ s, c i * (a i / D i))| ≤
      C * δ / d^2
```

### normalized_surviving_mass_le

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section3DenominatorReplacement.lean:56)

The actual surviving normalized rates have total mass at most one.

```lean
theorem normalized_surviving_mass_le (w : WeightArray) (hnorm : NormalizedWeights w)
    (n : ℕ) (s : Finset (Fin (n + 1))) (E τ : Fin (n + 1) → ℝ) :
    ∑ i ∈ s, ((w (n + 1)).rate i * survivalGe (τ i) (E i)) / (n + 1 : ℕ) ≤ 1
```

### denominator_replacement_converges

theorem; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section3DenominatorReplacement.lean:78)

Equation `eq:p-first-approx` for arbitrary uniformly bounded signed
coefficients on the interior labels. All random-denominator control is
proved from normalization and the original profile assumption.

```lean
theorem denominator_replacement_converges
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (s : ∀ n, Finset (Fin (n + 1)))
    (hs : ∀ n i, i ∈ s n → ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α)
    (g : ∀ n, Fin (n + 1) → ℝ) {G : ℝ}
    (hG : 0 ≤ G) (hg : ∀ n i, i ∈ s n → |g n i| ≤ G) :
    ConvergesInProbability (fun n => exponentialRace (w (n + 1)))
      (fun n E => (∑ i ∈ s n, g n i * predictableChance (w (n + 1)) (raceDraw E) i) -
        (∑ i ∈ s n,
          (g n i / profileD profileMeasure f
            (profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ)))) *
          (w (n + 1)).rate i * survivalGe (orderTime E i) (E i)) / (n + 1 : ℕ)) 0
```


## Luce/Section3Expectation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace Luce
```

### profileGridEndpoint

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:22)

Right endpoint of the cell containing a positive location.

```lean
def profileGridEndpoint (n : ℕ) (x : ℝ) : ℝ :=
  (⌈x * (n + 1 : ℕ)⌉₊ : ℝ) / (n + 1 : ℕ)
```

### profileGridEndpoint_ge

lemma; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:25)

```lean
lemma profileGridEndpoint_ge (n : ℕ) (x : ℝ) : x ≤ profileGridEndpoint n x
```

### profileGridEndpoint_pos

lemma; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:29)

```lean
lemma profileGridEndpoint_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < profileGridEndpoint n x
```

### profileGridEndpoint_of_mem_cell

lemma; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:32)

```lean
lemma profileGridEndpoint_of_mem_cell (n : ℕ) (i : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioc ((i.val : ℝ) / (n + 1 : ℕ))
      (((i.val : ℝ) + 1) / (n + 1 : ℕ))) :
    profileGridEndpoint n x = ((i.val : ℝ) + 1) / (n + 1 : ℕ)
```

### tendsto_profileGridEndpoint

lemma; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:48)

```lean
lemma tendsto_profileGridEndpoint {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => profileGridEndpoint n x) atTop (𝓝 x)
```

### measurable_comp_profileGridEndpoint

lemma; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:53)

```lean
lemma measurable_comp_profileGridEndpoint (n : ℕ) (h : ℝ → ℝ) :
    Measurable (fun x => h (profileGridEndpoint n x))
```

### measurable_profileGridEndpoint

lemma; [source line 58](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:58)

```lean
lemma measurable_profileGridEndpoint (n : ℕ) : Measurable (profileGridEndpoint n)
```

### profileGridKernel

def; [source line 63](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:63)

The label sum, expressed as a function constant in its label parameters
on each cell, with an arbitrary rate profile in the last argument.

```lean
def profileGridKernel (n : ℕ) (α : ℝ) (c t f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 < x ∧ profileGridEndpoint n x ≤ α then
    c (profileGridEndpoint n x) * rateKernel (t (profileGridEndpoint n x)) (f x)
  else 0
```

### aestronglyMeasurable_profileGridKernel

lemma; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:68)

```lean
lemma aestronglyMeasurable_profileGridKernel (n : ℕ) (α : ℝ) (c t : ℝ → ℝ)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f profileMeasure) :
    AEStronglyMeasurable (profileGridKernel n α c t f) profileMeasure
```

### abs_profileGridKernel_le

lemma; [source line 82](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:82)

```lean
lemma abs_profileGridKernel_le {n : ℕ} {α C : ℝ} {c t f : ℝ → ℝ}
    (hC : 0 ≤ C) (hc : ∀ y ∈ Icc (0 : ℝ) α, |c y| ≤ C)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) {x : ℝ} (hf : 0 ≤ f x) :
    |profileGridKernel n α c t f x| ≤ C * f x
```

### integrable_profileGridKernel

lemma; [source line 95](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:95)

```lean
lemma integrable_profileGridKernel {n : ℕ} {α C : ℝ} {c t f : ℝ → ℝ}
    (hC : 0 ≤ C) (hc : ∀ y ∈ Icc (0 : ℝ) α, |c y| ≤ C)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    (hf : Integrable f profileMeasure) (hf₀ : ∀ᵐ x ∂profileMeasure, 0 ≤ f x) :
    Integrable (profileGridKernel n α c t f) profileMeasure
```

### abs_profileGridKernel_sub_le

lemma; [source line 106](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:106)

The global one-Lipschitz bound in the rate is preserved with variable
cellwise times. This supplies the uniform L¹ error in lines 792–797.

```lean
lemma abs_profileGridKernel_sub_le {n : ℕ} {α C : ℝ} {c t f g : ℝ → ℝ}
    (hC : 0 ≤ C) (hc : ∀ y ∈ Icc (0 : ℝ) α, |c y| ≤ C)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) {x : ℝ}
    (hf : 0 ≤ f x) (hg : 0 ≤ g x) :
    |profileGridKernel n α c t f x - profileGridKernel n α c t g x| ≤
      C * |f x - g x|
```

### profileLimitKernel

def; [source line 121](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:121)

```lean
def profileLimitKernel (α : ℝ) (c t f : ℝ → ℝ) : ℝ → ℝ :=
  (Ioc (0 : ℝ) α).indicator (fun x => c x * rateKernel (t x) (f x))
```

### tendsto_profileGridKernel

lemma; [source line 124](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:124)

```lean
lemma tendsto_profileGridKernel {α : ℝ} {c t f : ℝ → ℝ}
    (hc : ContinuousOn c (Icc (0 : ℝ) α)) (ht : ContinuousOn t (Icc (0 : ℝ) α))
    {x : ℝ} (hx : 0 < x) (hxa : x ≠ α) :
    Tendsto (fun n => profileGridKernel n α c t f x) atTop
      (𝓝 (profileLimitKernel α c t f x))
```

### ae_tendsto_profileGridKernel

lemma; [source line 150](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:150)

```lean
lemma ae_tendsto_profileGridKernel {α : ℝ} {c t f : ℝ → ℝ}
    (hc : ContinuousOn c (Icc (0 : ℝ) α)) (ht : ContinuousOn t (Icc (0 : ℝ) α)) :
    ∀ᵐ x ∂profileMeasure, Tendsto (fun n => profileGridKernel n α c t f x) atTop
      (𝓝 (profileLimitKernel α c t f x))
```

### integrable_profileLimitKernel

lemma; [source line 160](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:160)

Integrability of the actual limiting diagonal-type integrand is proved,
so its real integral never uses a value assigned to a nonintegrable function.

```lean
lemma integrable_profileLimitKernel {α C : ℝ} {c t f : ℝ → ℝ}
    (hC : 0 ≤ C) (hc : ContinuousOn c (Icc (0 : ℝ) α))
    (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (hcC : ∀ y ∈ Icc (0 : ℝ) α, |c y| ≤ C)
    (ht₀ : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    (hf : Integrable f profileMeasure) (hf₀ : ∀ᵐ x ∂profileMeasure, 0 ≤ f x) :
    Integrable (profileLimitKernel α c t f) profileMeasure
```

### tendsto_integral_profileGridKernel

theorem; [source line 177](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:177)

Dominated convergence at the fixed limiting profile handles unbounded f
and the cells touching zero without a pointwise bound on f.

```lean
theorem tendsto_integral_profileGridKernel {α C : ℝ} {c t f : ℝ → ℝ}
    (hC : 0 ≤ C) (hc : ContinuousOn c (Icc (0 : ℝ) α))
    (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (hcC : ∀ y ∈ Icc (0 : ℝ) α, |c y| ≤ C)
    (ht₀ : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    (hf : Integrable f profileMeasure) (hf₀ : ∀ᵐ x ∂profileMeasure, 0 ≤ f x) :
    Tendsto (fun n => ∫ x, profileGridKernel n α c t f x ∂profileMeasure) atTop
      (𝓝 (∫ x, profileLimitKernel α c t f x ∂profileMeasure))
```

### ProfileLimit.tendsto_integral_gridKernel

theorem; [source line 194](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:194)

L¹ perturbation from the paper's actual step profiles to the limit,
uniformly over all right-endpoint times.

```lean
theorem ProfileLimit.tendsto_integral_gridKernel {w : WeightArray} {f c t : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : 0 ≤ α)
    (hc : ContinuousOn c (Icc (0 : ℝ) α)) (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht₀ : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) :
    Tendsto (fun n => ∫ x, profileGridKernel n α c t (stepProfile w (n + 1)) x
      ∂profileMeasure) atTop (𝓝 (∫ x, profileLimitKernel α c t f x ∂profileMeasure))
```

### profileGridKernel_step_eq_sum

lemma; [source line 224](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:224)

```lean
private lemma profileGridKernel_step_eq_sum (w : WeightArray) (n : ℕ) (α : ℝ)
    (c t : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    profileGridKernel n α c t (stepProfile w (n + 1)) x =
      ∑ i : Fin (n + 1), if (i.val : ℝ) / (n + 1 : ℕ) < x ∧
        x ≤ ((i.val : ℝ) + 1) / (n + 1 : ℕ) then
          (if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α then
            c (((i.val : ℝ) + 1) / (n + 1 : ℕ)) *
              rateKernel (t (((i.val : ℝ) + 1) / (n + 1 : ℕ))) ((w (n + 1)).rate i)
          else 0) else 0
```

### integral_profileGridKernel_step

theorem; [source line 256](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:256)

Exact normalized finite expectation sum. The last fractional cell is
included precisely when its right endpoint lies at or below α.

```lean
theorem integral_profileGridKernel_step (w : WeightArray) (n : ℕ) (α : ℝ)
    (c t : ℝ → ℝ) :
    (∫ x, profileGridKernel n α c t (stepProfile w (n + 1)) x ∂profileMeasure) =
      (∑ i : Fin (n + 1), if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α then
        c (((i.val : ℝ) + 1) / (n + 1 : ℕ)) *
          rateKernel (t (((i.val : ℝ) + 1) / (n + 1 : ℕ))) ((w (n + 1)).rate i)
      else 0) / (n + 1 : ℕ)
```

### integral_profileLimitKernel_eq

lemma; [source line 286](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:286)

```lean
lemma integral_profileLimitKernel_eq {α : ℝ} (hα : α < 1) (c t f : ℝ → ℝ) :
    (∫ x, profileLimitKernel α c t f x ∂profileMeasure) =
      ∫ x in Ioc (0 : ℝ) α, c x * rateKernel (t x) (f x)
```

### ProfileLimit.integrable_expectation_limit

theorem; [source line 297](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:297)

Finiteness of the limiting weighted diagonal integral follows from the
original profile hypothesis and continuous coefficients on the bulk.

```lean
theorem ProfileLimit.integrable_expectation_limit
    {w : WeightArray} {f c t : ℝ → ℝ} (hf : ProfileLimit w f) {α : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hc : ContinuousOn c (Icc (0 : ℝ) α)) (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht₀ : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) :
    IntegrableOn (fun x => c x * rateKernel (t x) (f x)) (Ioc (0 : ℝ) α)
```

### ProfileLimit.deterministic_expectation_limit

theorem; [source line 316](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Expectation.lean:316)

The deterministic expectation limit (lines 781–797), for arbitrary
continuous coefficient and nonnegative continuous arrival-time functions.
There is no boundedness or continuity assumption on the limiting profile.
Taking `c x = g x / D(t x)` recovers the expression in the manuscript.

```lean
theorem ProfileLimit.deterministic_expectation_limit
    {w : WeightArray} {f c t : ℝ → ℝ} (hf : ProfileLimit w f) {α : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hc : ContinuousOn c (Icc (0 : ℝ) α)) (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht₀ : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) :
    Tendsto (fun n =>
      (∑ i : Fin (n + 1), if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α then
        c (((i.val : ℝ) + 1) / (n + 1 : ℕ)) *
          rateKernel (t (((i.val : ℝ) + 1) / (n + 1 : ℕ))) ((w (n + 1)).rate i)
      else 0) / (n + 1 : ℕ)) atTop
      (𝓝 (∫ x in Ioc (0 : ℝ) α, c x * rateKernel (t x) (f x)))
```


## Luce/Section3InitialBlock.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3InitialBlock.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### initialRateMass

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section3InitialBlock.lean:21)

The paper's sum over all positive labels whose spatial coordinate is
at most the cutoff. Nonpositive cutoffs automatically select no labels.

```lean
def initialRateMass (w : WeightArray) (n : ℕ) (η : ℝ) : ℝ :=
  (∑ i : Fin (n + 1), if ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ η
    then (w (n + 1)).rate i else 0) / (n + 1 : ℕ)
```

### initialRateMass_le_integral

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section3InitialBlock.lean:27)

Every selected label contributes precisely the mass of its entire cell;
the last fractional cell can only increase the upper bound on the right.

```lean
theorem initialRateMass_le_integral (w : WeightArray) (n : ℕ) (η : ℝ) :
    initialRateMass w n η ≤ ∫ x in Ioc (0 : ℝ) η, stepProfile w (n + 1) x ∂profileMeasure
```

### initialRateMass_le_limit_add_error

theorem; [source line 70](D:/princeton/Research/Lean/Lean_luce/Luce/Section3InitialBlock.lean:70)

Quantitative L¹ comparison for the initial label block.

```lean
theorem initialRateMass_le_limit_add_error {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (n : ℕ) (η : ℝ) :
    initialRateMass w n η ≤ (∫ x in Ioc (0 : ℝ) η, f x ∂profileMeasure) +
      ∫ x, |stepProfile w (n + 1) x - f x| ∂profileMeasure
```

### ProfileLimit.initial_mass_small

theorem; [source line 89](D:/princeton/Research/Lean/Lean_luce/Luce/Section3InitialBlock.lean:89)

The double-limit initial-block estimate actually used in Section 3.

```lean
theorem ProfileLimit.initial_mass_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, initialRateMass w n η < ε
```


## Luce/Section3Intensity.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Intensity.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce
```

### interiorDensityMeasure

def; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Intensity.lean:24)

The real-line intensity in Corollary 3.3. The exclusion of zero is
immaterial for Lebesgue measure and avoids assigning a profile value there.

```lean
def interiorDensityMeasure (f : ℝ → ℝ) (α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (0 : ℝ) α)).withDensity (fun x => ENNReal.ofReal (profileDiagonal f x))
```

### profileDiagonal_nonneg

lemma; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Intensity.lean:27)

```lean
lemma profileDiagonal_nonneg {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) α) :
    0 ≤ profileDiagonal f x
```

### integrable_profileDiagonal

lemma; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Intensity.lean:36)

```lean
lemma integrable_profileDiagonal {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    Integrable (profileDiagonal f) (volume.restrict (Ioc (0 : ℝ) α))
```

### interiorDensityMeasure_finite

lemma; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Intensity.lean:42)

```lean
lemma interiorDensityMeasure_finite {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    IsFiniteMeasure (interiorDensityMeasure f α)
```

### interiorIntensity

def; [source line 49](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Intensity.lean:49)

Compact-interval representation of the manuscript's intensity; the
finiteness proof is derived from Assumption 1.1.

```lean
def interiorIntensity (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f)
    (α : ℝ) (hα : α < 1) : FiniteMeasure (Icc (0 : ℝ) 1) :=
  FiniteMeasure.map (⟨interiorDensityMeasure f α, interiorDensityMeasure_finite hf hα⟩ : FiniteMeasure ℝ)
    (Set.projIcc (0 : ℝ) 1 zero_le_one)
```

### interiorDensityMeasure_ae_mem

lemma; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Intensity.lean:54)

```lean
lemma interiorDensityMeasure_ae_mem (f : ℝ → ℝ) (α : ℝ) :
    ∀ᵐ x ∂interiorDensityMeasure f α, x ∈ Ioc (0 : ℝ) α
```

### interiorIntensity_projection_recovery

theorem; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Intensity.lean:61)

Exact recovery of the real-line intensity. The projection changes no
point on the support of the density measure.

```lean
theorem interiorIntensity_projection_recovery (w : WeightArray) (f : ℝ → ℝ)
    (hf : ProfileLimit w f) (α : ℝ) (hα : α < 1) :
    (interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1)).map Subtype.val =
      interiorDensityMeasure f α
```

### integrable_interiorIntensity

theorem; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Intensity.lean:78)

Continuous spatial tests are genuinely integrable under the finite
intensity measure, independently of totalized integral conventions.

```lean
theorem integrable_interiorIntensity (w : WeightArray) (f : ℝ → ℝ)
    (hf : ProfileLimit w f) (α : ℝ) (hα : α < 1)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    Integrable g (interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1))
```

### integral_interiorIntensity

theorem; [source line 86](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Intensity.lean:86)

The continuous-test identity needed to apply Proposition 3.2 to the
actual intensity measure, with precisely the diagonal density.

```lean
theorem integral_interiorIntensity (w : WeightArray) (f : ℝ → ℝ)
    (hf : ProfileLimit w f) (α : ℝ) (hα : α < 1)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    (∫ y, g y ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1))) =
      ∫ x in Ioc (0 : ℝ) α,
        g (Set.projIcc (0 : ℝ) 1 zero_le_one x) * profileDiagonal f x
```


## Luce/Section3LuceCompensator.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3LuceCompensator.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### luce_event_probability

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section3LuceCompensator.lean:21)

All finite permutation events have the same probabilities under the
defining Luce law and the proved exponential-race representation.

```lean
theorem luce_event_probability {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ)
    (s : Set (Equiv.Perm (Fin n))) :
    P (π ⁻¹' s) = exponentialRace w (raceDraw ⁻¹' s)
```

### luceInteriorCompensatorSum

def; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section3LuceCompensator.lean:36)

The literal weighted predictable sum, in terms of the draw permutation
rather than a choice of an underlying clock representation.

```lean
def luceInteriorCompensatorSum {n : ℕ} (w : Weights n) (g : ℝ → ℝ)
    (α : ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ k : Fin n, if ((k.val : ℝ) + 1) / n ≤ α then
    g (((k.val : ℝ) + 1) / n) * predictableChance w π k else 0
```

### luceInteriorCompensatorSum_race

lemma; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section3LuceCompensator.lean:41)

```lean
lemma luceInteriorCompensatorSum_race {n : ℕ} (w : Weights n)
    (g : ℝ → ℝ) (α : ℝ) (clocks : Fin n → ℝ) :
    luceInteriorCompensatorSum w g α (raceDraw clocks) =
      interiorCompensatorSum w g α clocks
```

### section3_weighted_compensator_luce

theorem; [source line 49](D:/princeton/Research/Lean/Lean_luce/Luce/Section3LuceCompensator.lean:49)

Proposition 3.2, `eq:weighted-compensator`, on an arbitrary Luce-law
model. Every continuous test on the exact source interval is admitted.
Its total extension is proved to equal the original test on that interval.

```lean
theorem section3_weighted_compensator_luce
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ)
    {α : ℝ} (hα : α < 1) (g : Icc (0 : ℝ) α → ℝ) (hg : Continuous g) :
    ConvergesInProbability P
      (fun n ω => luceInteriorCompensatorSum (w n) (intervalTestExtension α g) α (π n ω))
      (∫ x in Ioc (0 : ℝ) α, intervalTestExtension α g x * profileDiagonal f x)
```

### section3_max_probability_luce

theorem; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section3LuceCompensator.lean:80)

Proposition 3.2, `eq:interior-max-p`, for every measurable permutation
having exactly the manuscript's Luce masses.

```lean
theorem section3_max_probability_luce
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ)
    {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
        ε ≤ predictableChance (w n) (π n ω) k}) atTop (𝓝 0)
```


## Luce/Section3LuceLaw.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3LuceLaw.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce
```

### luce_map_eq_raceDraw

theorem; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section3LuceLaw.lean:18)

The defining Luce masses identify the law of any measurable permutation
with the law of the sorted independent exponential clocks.

```lean
theorem luce_map_eq_raceDraw {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ) :
    @Measure.map Ω (Equiv.Perm (Fin n)) mΩ ⊤ π P =
      @Measure.map (Fin n → ℝ) (Equiv.Perm (Fin n)) inferInstance ⊤
        raceDraw (exponentialRace w)
```


## Luce/Section3Mean.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Mean.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### section3_cell_unique

lemma; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Mean.lean:18)

```lean
private lemma section3_cell_unique {n : ℕ} {i j : Fin n} {x : ℝ}
    (hi : (i.val : ℝ) / n < x ∧ x ≤ ((i.val : ℝ) + 1) / n)
    (hj : (j.val : ℝ) / n < x ∧ x ≤ ((j.val : ℝ) + 1) / n) : i = j
```

### comp_stepProfile_eq_sum

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Mean.lean:33)

A kernel that vanishes at zero acts cellwise on the literal profile.
This requires no continuity or measurability of the kernel.

```lean
theorem comp_stepProfile_eq_sum (w : WeightArray) (n : ℕ) (φ : ℝ → ℝ)
    (hφ : φ 0 = 0) (x : ℝ) :
    φ (stepProfile w n x) = ∑ i : Fin n,
      if (i.val : ℝ) / n < x ∧ x ≤ ((i.val : ℝ) + 1) / n
      then φ ((w n).rate i) else 0
```

### section3_cell_real_measure

theorem; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Mean.lean:62)

Every half-open profile cell has precisely its stated length under
Lebesgue measure restricted to `(0,1)`.

```lean
theorem section3_cell_real_measure {n : ℕ} (i : Fin n) :
    profileMeasure.real (Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)) = 1 / n
```

### integral_comp_stepProfile

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Mean.lean:81)

The exact finite-cell integral underlying both means (670–679).
Even a nonmeasurable kernel has a measurable finite-valued composition here.

```lean
theorem integral_comp_stepProfile (w : WeightArray) (n : ℕ) (φ : ℝ → ℝ)
    (hφ : φ 0 = 0) :
    (∫ x, φ (stepProfile w n x) ∂profileMeasure) =
      (∑ i : Fin n, φ ((w n).rate i)) / n
```

### meanRemaining_eq_profileD

theorem; [source line 109](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Mean.lean:109)

The finite rate mean equals the transform of the actual step profile.

```lean
theorem meanRemaining_eq_profileD (w : WeightArray) (n : ℕ) (t : ℝ) :
    meanRemaining (w n) t = profileD profileMeasure (stepProfile w n) t
```

### meanArrival_eq_profileF

theorem; [source line 115](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Mean.lean:115)

The finite arrival mean equals the actual profile transform, also on
the empty row: both sides are zero there.

```lean
theorem meanArrival_eq_profileF (w : WeightArray) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    meanArrival (w n) t = profileF profileMeasure (stepProfile w n) t
```


## Luce/Section3OrderStats.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3OrderStats.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### orderTime

def; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section3OrderStats.lean:23)

A total version of the `k+1`st order statistic. The value on tied clock
configurations is irrelevant because their probability is proved to be zero.

```lean
def orderTime {n : ℕ} (clocks : Fin n → ℝ) (k : Fin n) : ℝ :=
  if h : Function.Injective clocks then arrivalTime clocks h k else 0
```

### orderTime_eq_arrivalTime

lemma; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section3OrderStats.lean:26)

```lean
lemma orderTime_eq_arrivalTime {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (k : Fin n) :
    orderTime clocks k = arrivalTime clocks hinj k
```

### draw_arrivalTime_le_iff

lemma; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section3OrderStats.lean:31)

```lean
lemma draw_arrivalTime_le_iff {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (j k : Fin n) :
    clocks (drawPermutation clocks hinj j) ≤ arrivalTime clocks hinj k ↔ j ≤ k
```

### empiricalArrival_orderTime

theorem; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section3OrderStats.lean:42)

The CDF at the `k+1`st distinct arrival is exactly `(k+1)/n`. This
counts every label once by the proved draw-order permutation.

```lean
theorem empiricalArrival_orderTime {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (k : Fin n) :
    empiricalArrival clocks (orderTime clocks k) = ((k.val : ℝ) + 1) / n
```

### exponentialRace_nonneg_ae

theorem; [source line 58](D:/princeton/Research/Lean/Lean_luce/Luce/Section3OrderStats.lean:58)

```lean
theorem exponentialRace_nonneg_ae {n : ℕ} (w : Weights n) :
    ∀ᵐ clocks ∂exponentialRace w, ∀ i, 0 ≤ clocks i
```

### orderTime_nonneg

lemma; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section3OrderStats.lean:66)

```lean
lemma orderTime_nonneg {n : ℕ} (clocks : Fin n → ℝ)
    (hclocks : ∀ i, 0 ≤ clocks i) (k : Fin n) : 0 ≤ orderTime clocks k
```

### section3_uniform_quantile

theorem; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section3OrderStats.lean:76)

Equation `eq:uniform-quantile`, with the exact positive row shift and
one-based spatial coordinate. The proof uses the manuscript's empirical
CDF convergence and uniform continuity of its inverse.

```lean
theorem section3_uniform_quantile
    (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f) {α : ℝ}
    (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ |orderTime clocks k -
          profileQuantile profileMeasure f (((k.val : ℝ) + 1) / (n + 1 : ℕ))|})
      atTop (𝓝 0)
```

### section3_uniform_denominator

theorem; [source line 140](D:/princeton/Research/Lean/Lean_luce/Luce/Section3OrderStats.lean:140)

Random-time substitution in the remaining-rate process, completing
equation `eq:uniform-denominator`. The comparison times and empirical times
are confined to one compact interval before applying continuity of `D`.

```lean
theorem section3_uniform_denominator
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ |empiricalRemainingGe (w (n + 1)) clocks (orderTime clocks k) -
          profileD profileMeasure f
            (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / (n + 1 : ℕ)))|})
      atTop (𝓝 0)
```

### section3_order_statistics_general

theorem; [source line 235](D:/princeton/Research/Lean/Lean_luce/Luce/Section3OrderStats.lean:235)

The last two conclusions of Lemma 3.1 on arbitrary probability spaces,
with the original row index `n`. Independence and the exponential marginal
laws are the manuscript's race representation; no concentration conclusion
is assumed. The empty row is handled by the proved filter shift.

```lean
theorem section3_order_statistics_general
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) {α : ℝ} (hα : α < 1) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
        ε ≤ |orderTime (fun i => E n i ω) k -
          profileQuantile profileMeasure f (((k.val : ℝ) + 1) / n)|})
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
        ε ≤ |empiricalRemainingGe (w n) (fun i => E n i ω)
            (orderTime (fun i => E n i ω) k) -
          profileD profileMeasure f
            (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / n))|})
      atTop (𝓝 0))
```


## Luce/Section3Poisson.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal BoundedContinuousFunction
namespace Luce
```

### section3Location

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:21)

The paper's one-based location, in the compact ambient interval.

```lean
def section3Location (n : ℕ) (k : Fin n) : Icc (0 : ℝ) 1 :=
  ⟨((k.val : ℝ) + 1) / n, by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
    constructor
    · exact div_nonneg (by positivity) hn.le
    · apply (div_le_iff₀ hn).mpr
      simpa only [one_mul] using
        (show (k.val : ℝ) + 1 ≤ n by exact_mod_cast Nat.succ_le_of_lt k.isLt)⟩
```

### interiorFixedPoints

def; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:32)

The literal fixed-point process restricted to `[0,α]`, for a draw
permutation. The inverse rank convention is retained in the definition.

```lean
def interiorFixedPoints {n : ℕ} (α : ℝ) (π : Equiv.Perm (Fin n)) :
    FinitePointMeasure (Icc (0 : ℝ) 1) :=
  observedPointMeasure (section3Location n)
    (fun k => decide (((k.val : ℝ) + 1) / n ≤ α ∧ π.symm k = k))
```

### interiorFixedPoints_toFiniteMeasure

theorem; [source line 39](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:39)

This representation is exactly the sum of unit Dirac masses in
`eq:fixed-process`; every selected label contributes once.

```lean
theorem interiorFixedPoints_toFiniteMeasure {n : ℕ} (α : ℝ)
    (π : Equiv.Perm (Fin n)) :
    (interiorFixedPoints α π).toFiniteMeasure =
      ∑ k : Fin n, if ((k.val : ℝ) + 1) / n ≤ α ∧ π.symm k = k then
        (diracProba (section3Location n k)).toFiniteMeasure else 0
```

### raceInteriorBernoulli_pointMeasure

theorem; [source line 47](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:47)

```lean
theorem raceInteriorBernoulli_pointMeasure {n : ℕ} (w : Weights n)
    (α : ℝ) (E : Fin n → ℝ) :
    (raceInteriorBernoulli w α).pointMeasure (section3Location n) E =
      interiorFixedPoints α (raceDraw E)
```

### section3_convergence_congr_ae

lemma; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:56)

```lean
lemma section3_convergence_congr_ae
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} {X Y : ∀ n, Ω n → ℝ} {c : ℝ}
    (hY : ConvergesInProbability P Y c) (heq : ∀ n, X n =ᵐ[P n] Y n) :
    ConvergesInProbability P X c
```

### section3_rowMaximum_lt

lemma; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:73)

```lean
lemma section3_rowMaximum_lt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (B : BernoulliProcess P) (N : ℕ) (ω : Ω)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ k < N, B.probability k ω < ε) → B.rowMaximum N ω < ε
```

### raceInteriorBernoulli_integral

theorem; [source line 86](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:86)

The compensator of the actual adapted indicator row agrees almost
everywhere with the explicit sum proved in Proposition 3.2.

```lean
theorem raceInteriorBernoulli_integral {n : ℕ} (w : Weights n) (α : ℝ)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    (fun E => ∫ y, g y ∂((raceInteriorBernoulli w α).predictableMeasure
      (section3Location n) E : Measure (Icc (0 : ℝ) 1))) =ᵐ[exponentialRace w]
    (fun E => interiorCompensatorSum w
      (fun x => g (projIcc 0 1 zero_le_one x)) α E)
```

### section3_predictable_tests

theorem; [source line 110](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:110)

Both hypotheses of the Section 2 criterion are proved for the actual
interior row. No conditional-mean or small-maximum assumption remains.

```lean
theorem section3_predictable_tests
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    ConvergesInProbability (fun n => exponentialRace (w n))
      (fun n E => ∫ y, g y ∂((raceInteriorBernoulli (w n) α).predictableMeasure
        (section3Location n) E : Measure (Icc (0 : ℝ) 1)))
      (∫ y, g y ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1)))
```

### section3_predictable_maximum

theorem; [source line 127](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:127)

```lean
theorem section3_predictable_maximum
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ConvergesInProbability (fun n => exponentialRace (w n))
      (fun n => (raceInteriorBernoulli (w n) α).toProcess.rowMaximum n) 0
```

### section3_interior_poisson

theorem; [source line 168](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:168)

Corollary 3.3, convergence in law of the actual finite point measure.
The limit is constructed as a Poisson count of iid intensity-distributed
locations. Its independent-count PRM characterization is proved separately
in `Section3PoissonLaw`, rather than postulated by a definition.

```lean
theorem section3_interior_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ E,
      F (interiorFixedPoints α (raceDraw E)) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (interiorIntensity w f hf α hα)))
```

### section3_interior_poisson_general

theorem; [source line 185](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Poisson.lean:185)

Corollary 3.3 for every Luce permutation model, on arbitrary row
probability spaces. The full masses in `eq:luce-law` are the defining
distribution of the paper's model, not additional asymptotic assumptions.

```lean
theorem section3_interior_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ)
    {α : ℝ} (hα : α < 1) (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (interiorFixedPoints α (π n ω)) ∂P n) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (interiorIntensity w f hf α hα)))
```


## Luce/Section3PoissonCriterion.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonCriterion.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter Topology
open scoped NNReal BoundedContinuousFunction BigOperators
namespace Luce
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
```

### totalPredictable_of_integrals

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonCriterion.lean:24)

```lean
theorem totalPredictable_of_integrals
    (htest : ∀ g : X →ᵇ ℝ, ConvergesInProbability P
      (fun n ω => ∫ y, g y ∂((B n).predictableMeasure (x n) ω : Measure X))
      (∫ y, g y ∂(ν : Measure X))) :
    ConvergesInProbability P
      (fun n ω => ∑ k ∈ Finset.range n, (B n).toProcess.probability k ω)
      (ν.mass : ℝ)
```

### pointMeasure_laplace_of_integrals

theorem; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonCriterion.lean:38)

```lean
theorem pointMeasure_laplace_of_integrals
    (htest : ∀ g : X →ᵇ ℝ, ConvergesInProbability P
      (fun n ω => ∫ y, g y ∂((B n).predictableMeasure (x n) ω : Measure X))
      (∫ y, g y ∂(ν : Measure X)))
    (hmax : ConvergesInProbability P (fun n => (B n).toProcess.rowMaximum n) 0)
    (g : X →ᵇ ℝ≥0) :
    Tendsto (fun n => ∫ ω,
      pointLaplace (fun z => (g z : ℝ)) ((B n).pointMeasure (x n) ω) ∂P n)
      atTop (𝓝 (∫ s, pointLaplace (fun z => (g z : ℝ)) s ∂finitePoissonLaw ν))
```

### predictable_poisson_of_integrals

theorem; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonCriterion.lean:80)

The full law conclusion of Lemma 2.1, with its compensator assumption
supplied one continuous test at a time by Proposition 3.2.

```lean
theorem predictable_poisson_of_integrals
    (htest : ∀ g : X →ᵇ ℝ, ConvergesInProbability P
      (fun n ω => ∫ y, g y ∂((B n).predictableMeasure (x n) ω : Measure X))
      (∫ y, g y ∂(ν : Measure X)))
    (hmax : ConvergesInProbability P (fun n => (B n).toProcess.rowMaximum n) 0)
    (F : FinitePointMeasure X →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F ((B n).pointMeasure (x n) ω) ∂P n)
      atTop (𝓝 (∫ μ, F μ ∂finitePoissonLaw ν))
```


## Luce/Section3PoissonLaw.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators NNReal ENNReal BoundedContinuousFunction
namespace Luce
section Counts
variable {X : Type*} [MeasurableSpace X]
```

### NatCountVector

abbrev; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:22)

```lean
abbrev NatCountVector (m : ℕ) := Fin m → ℕ
```

### natCountLaplace

def; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:24)

```lean
def natCountLaplace (m : ℕ) (t : Fin m → ℝ≥0) : C(NatCountVector m, ℝ) :=
  ⟨fun a => Real.exp (-(∑ i, (t i : ℝ) * (a i : ℝ))), continuous_of_discreteTopology⟩
```

### natCountLaplace_zero

lemma; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:27)

```lean
lemma natCountLaplace_zero (m : ℕ) : natCountLaplace m 0 = 1
```

### natCountLaplace_add

lemma; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:31)

```lean
lemma natCountLaplace_add (m : ℕ) (t u : Fin m → ℝ≥0) :
    natCountLaplace m (t + u) = natCountLaplace m t * natCountLaplace m u
```

### natCountLaplaceMonoid

def; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:36)

```lean
def natCountLaplaceMonoid (m : ℕ) : Submonoid C(NatCountVector m, ℝ) where
  carrier := Set.range (natCountLaplace m)
  one_mem' := ⟨0, natCountLaplace_zero m⟩
  mul_mem' := by
    rintro a b ⟨t, rfl⟩ ⟨u, rfl⟩
    exact ⟨t + u, natCountLaplace_add m t u⟩
```

### natCountLaplaceAlgebra

def; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:43)

```lean
def natCountLaplaceAlgebra (m : ℕ) : Subalgebra ℝ C(NatCountVector m, ℝ) :=
  Algebra.adjoin ℝ (natCountLaplaceMonoid m : Set C(NatCountVector m, ℝ))
```

### natCountLaplaceAlgebra_eq_span

lemma; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:46)

```lean
lemma natCountLaplaceAlgebra_eq_span (m : ℕ) :
    (natCountLaplaceAlgebra m).toSubmodule =
      Submodule.span ℝ (Set.range (natCountLaplace m))
```

### natCountLaplaceAlgebra_separatesPoints

lemma; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:52)

```lean
lemma natCountLaplaceAlgebra_separatesPoints (m : ℕ) :
    (natCountLaplaceAlgebra m).SeparatesPoints
```

### norm_natCountLaplace_le_one

lemma; [source line 70](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:70)

```lean
lemma norm_natCountLaplace_le_one (m : ℕ) (t : Fin m → ℝ≥0) (a : NatCountVector m) :
    ‖natCountLaplace m t a‖ ≤ 1
```

### natCountLaplaceAlgebra_bounded

lemma; [source line 77](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:77)

```lean
lemma natCountLaplaceAlgebra_bounded (m : ℕ) (a : C(NatCountVector m, ℝ))
    (ha : a ∈ natCountLaplaceAlgebra m) : ∃ C : ℝ, ∀ x, ‖a x‖ ≤ C
```

### integrable_natCountLaplaceAlgebra

lemma; [source line 98](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:98)

```lean
lemma integrable_natCountLaplaceAlgebra (m : ℕ) (μ : Measure (NatCountVector m))
    [IsFiniteMeasure μ] (a : C(NatCountVector m, ℝ)) (ha : a ∈ natCountLaplaceAlgebra m) :
    Integrable a μ
```

### natCountBox

def; [source line 105](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:105)

```lean
def natCountBox (m N : ℕ) : Set (NatCountVector m) :=
  Set.range (fun a : Fin m → Fin (N + 1) => fun i => (a i).val)
```

### mem_natCountBox

lemma; [source line 108](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:108)

```lean
lemma mem_natCountBox (m N : ℕ) (a : NatCountVector m) :
    a ∈ natCountBox m N ↔ ∀ i, a i ≤ N
```

### natCountBox_compact

lemma; [source line 116](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:116)

```lean
lemma natCountBox_compact (m N : ℕ) : IsCompact (natCountBox m N)
```

### natCountBox_measurable

lemma; [source line 119](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:119)

```lean
lemma natCountBox_measurable (m N : ℕ) : MeasurableSet (natCountBox m N)
```

### natCountBox_eventually

lemma; [source line 122](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:122)

```lean
lemma natCountBox_eventually (m : ℕ) (a : NatCountVector m) :
    ∀ᶠ N in atTop, a ∈ natCountBox m N
```

### natCountBox_tail_tendsto

lemma; [source line 129](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:129)

```lean
lemma natCountBox_tail_tendsto (m : ℕ) (μ : Measure (NatCountVector m))
    [IsFiniteMeasure μ] : Tendsto (fun N => μ.real (natCountBox m N)ᶜ) atTop (𝓝 0)
```

### integral_natCountAlgebra_eq

lemma; [source line 148](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:148)

```lean
lemma integral_natCountAlgebra_eq (m : ℕ) (μ ν : Measure (NatCountVector m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hLaplace : ∀ t : Fin m → ℝ≥0,
      (∫ a, natCountLaplace m t a ∂μ) = ∫ a, natCountLaplace m t a ∂ν)
    (a : C(NatCountVector m, ℝ)) (ha : a ∈ natCountLaplaceAlgebra m) :
    (∫ x, a x ∂μ) = ∫ x, a x ∂ν
```

### natCountSingletonTest

def; [source line 178](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:178)

```lean
def natCountSingletonTest (m : ℕ) (a : NatCountVector m) : NatCountVector m →ᵇ ℝ where
  toFun b := if b = a then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  map_bounded' := ⟨1, fun x y => by
    rw [Real.dist_eq]
    split_ifs <;> norm_num⟩
```

### integral_natCountSingletonTest

lemma; [source line 185](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:185)

```lean
lemma integral_natCountSingletonTest (m : ℕ) (μ : Measure (NatCountVector m))
    (a : NatCountVector m) :
    (∫ b, natCountSingletonTest m a b ∂μ) = μ.real {a}
```

### natCountLaw_eq_of_laplace

theorem; [source line 199](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:199)

Nonnegative multivariate Laplace transforms determine a finite vector
of natural-number counts. The proof uses finite compact boxes and
Stone-Weierstrass, then actual singleton probabilities.

```lean
theorem natCountLaw_eq_of_laplace (m : ℕ) (μ ν : Measure (NatCountVector m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hLaplace : ∀ t : Fin m → ℝ≥0,
      (∫ a, natCountLaplace m t a ∂μ) = ∫ a, natCountLaplace m t a ∂ν) : μ = ν
```

### FinitePointMeasure.count_coe_eq

theorem; [source line 235](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:235)

The floor in the existing representation of a count loses no mass:
evaluation on every measurable set is precisely its natural count.

```lean
theorem FinitePointMeasure.count_coe_eq (ξ : FinitePointMeasure X)
    {A : Set X} (hA : MeasurableSet A) :
    (ξ.count A : ℝ) = (ξ.toFiniteMeasure A : ℝ)
```

### disjointCountTest

def; [source line 252](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:252)

```lean
def disjointCountTest (m : ℕ) (A : Fin m → Set X) (t : Fin m → ℝ≥0) (x : X) : ℝ :=
  ∑ i, (A i).indicator (fun _ => (t i : ℝ)) x
```

### measurable_disjointCountTest

lemma; [source line 255](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:255)

```lean
lemma measurable_disjointCountTest (m : ℕ) (A : Fin m → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (t : Fin m → ℝ≥0) :
    Measurable (disjointCountTest m A t)
```

### disjointCountTest_nonneg

lemma; [source line 261](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:261)

```lean
lemma disjointCountTest_nonneg (m : ℕ) (A : Fin m → Set X) (t : Fin m → ℝ≥0) (x : X) :
    0 ≤ disjointCountTest m A t x
```

### pointLaplace_disjointCountTest

lemma; [source line 267](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:267)

```lean
lemma pointLaplace_disjointCountTest (m : ℕ) (A : Fin m → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (t : Fin m → ℝ≥0) (ξ : FinitePointMeasure X) :
    pointLaplace (disjointCountTest m A t) ξ =
      natCountLaplace m t (fun i => ξ.count (A i))
```

### one_sub_exp_neg_disjointCountTest

lemma; [source line 285](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:285)

```lean
lemma one_sub_exp_neg_disjointCountTest (m : ℕ) (A : Fin m → Set X)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (t : Fin m → ℝ≥0) (x : X) :
    1 - Real.exp (-disjointCountTest m A t x) =
      ∑ i, (A i).indicator (fun _ => 1 - Real.exp (-(t i : ℝ))) x
```

### integral_one_sub_exp_neg_disjointCountTest

lemma; [source line 311](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:311)

```lean
lemma integral_one_sub_exp_neg_disjointCountTest (ν : FiniteMeasure X)
    (m : ℕ) (A : Fin m → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (t : Fin m → ℝ≥0) :
    (∫ x, 1 - Real.exp (-disjointCountTest m A t x) ∂(ν : Measure X)) =
      ∑ i, (ν (A i) : ℝ) * (1 - Real.exp (-(t i : ℝ)))
```

### integral_countLaplace_finitePoissonLaw

theorem; [source line 325](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:325)

The actual joint count Laplace transform of the canonical Poisson
construction, including arbitrary measurable disjoint sets of zero mass.

```lean
theorem integral_countLaplace_finitePoissonLaw (ν : FiniteMeasure X)
    (m : ℕ) (A : Fin m → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (t : Fin m → ℝ≥0) :
    (∫ ξ, natCountLaplace m t (fun i => ξ.count (A i)) ∂finitePoissonLaw ν) =
      Real.exp (-(∑ i, (ν (A i) : ℝ) * (1 - Real.exp (-(t i : ℝ)))))
```

### integral_natCountLaplace_pi_poisson

lemma; [source line 335](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:335)

```lean
lemma integral_natCountLaplace_pi_poisson (m : ℕ) (r : Fin m → ℝ≥0) (t : Fin m → ℝ≥0) :
    (∫ a, natCountLaplace m t a ∂Measure.pi (fun i => poissonMeasure (r i))) =
      Real.exp (-(∑ i, (r i : ℝ) * (1 - Real.exp (-(t i : ℝ)))))
```

### finitePoissonLaw_count_joint

theorem; [source line 364](D:/princeton/Research/Lean/Lean_luce/Luce/Section3PoissonLaw.lean:364)

The Poisson-count plus iid-location construction has exactly the
standard Poisson random-measure property: every finite family of disjoint
measurable sets has the product law of the corresponding scalar Poisson
counts. The spatial space need not be nonempty or standard Borel.

```lean
theorem finitePoissonLaw_count_joint (ν : FiniteMeasure X)
    (m : ℕ) (A : Fin m → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    (finitePoissonLaw ν).map (fun ξ i => ξ.count (A i)) =
      Measure.pi (fun i => poissonMeasure (ν (A i)))
```


## Luce/Section3Probability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Probability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### raceDraw

def; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Probability.lean:19)

Total extension of the draw order to the null event of tied clocks.

```lean
def raceDraw {n : ℕ} (clocks : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  if h : Function.Injective clocks then drawPermutation clocks h else Equiv.refl _
```

### raceDraw_eq

lemma; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Probability.lean:22)

```lean
lemma raceDraw_eq {n : ℕ} (clocks : Fin n → ℝ) (h : Function.Injective clocks) :
    raceDraw clocks = drawPermutation clocks h
```

### remaining_weight_eq_empirical

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Probability.lean:27)

The normalized remaining weight is exactly the weak empirical rate
evaluated at the arrival, including the arriving label itself.

```lean
theorem remaining_weight_eq_empirical {n : ℕ} (w : Weights n)
    (clocks : Fin n → ℝ) (hinj : Function.Injective clocks) (k : Fin n) :
    w.total (remaining (raceDraw clocks) k) / n =
      empiricalRemainingGe w clocks (orderTime clocks k)
```

### section3_denominator_lower

theorem; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Probability.lean:38)

The compact-interval denominator lower bound in line 752. It follows
from positivity of D and monotonicity of both D and the inverse time.

```lean
theorem section3_denominator_lower {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < profileD profileMeasure f (profileQuantile profileMeasure f α) ∧
      ∀ x ∈ Icc (0 : ℝ) α,
        profileD profileMeasure f (profileQuantile profileMeasure f α) ≤
          profileD profileMeasure f (profileQuantile profileMeasure f x)
```

### race_probability_le_on_good_event

theorem; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Probability.lean:54)

The pointwise bound of lines 802–803 on the good denominator event.

```lean
theorem race_probability_le_on_good_event (w : WeightArray) (n : ℕ)
    (clocks : Fin (n + 1) → ℝ) (hinj : Function.Injective clocks)
    (k : Fin (n + 1)) {D d : ℝ} (hd : 0 < d) (hdD : d ≤ D)
    (hclose : |empiricalRemainingGe (w (n + 1)) clocks (orderTime clocks k) - D| ≤ d/2) :
    predictableChance (w (n + 1)) (raceDraw clocks) k ≤
      2 * (rowMaxRate w n / (n + 1 : ℕ)) / d
```

### section3_max_probability

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Probability.lean:81)

Equation `eq:interior-max-p`, for the actual remaining-set ratio.
The bound on the maximum rate and the denominator convergence are both
derived from the manuscript assumptions in the proof.

```lean
theorem section3_max_probability
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ predictableChance (w (n + 1)) (raceDraw clocks) k}) atTop (𝓝 0)
```

### section3_max_probability_general

theorem; [source line 131](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Probability.lean:131)

The maximum conclusion of Proposition 3.2, with arbitrary row spaces
and the manuscript's original row index.

```lean
theorem section3_max_probability_general
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
        ε ≤ predictableChance (w n) (raceDraw (fun i => E n i ω)) k}) atTop (𝓝 0)
```


## Luce/Section3Profile.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal
namespace Luce
```

### instance at line 19

instance; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:19)

```lean
instance : IsFiniteMeasure profileMeasure := by
  unfold profileMeasure
  infer_instance
```

### instance at line 23

instance; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:23)

```lean
instance : IsProbabilityMeasure profileMeasure := by
  constructor
  simp [profileMeasure, Real.volume_Ioo]
```

### profileCell

def; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:29)

Open cells may replace the paper's half-open cells in integrals, because
the endpoints have Lebesgue measure zero.

```lean
def profileCell (n : ℕ) (i : Fin n) : Set ℝ :=
  Ioo ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)
```

### measurable_stepProfile

lemma; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:32)

```lean
lemma measurable_stepProfile (w : WeightArray) (n : ℕ) : Measurable (stepProfile w n)
```

### integrable_stepProfile

lemma; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:38)

```lean
lemma integrable_stepProfile (w : WeightArray) (n : ℕ) :
    Integrable (stepProfile w n) profileMeasure
```

### stepProfile_nonneg

lemma; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:53)

```lean
lemma stepProfile_nonneg (w : WeightArray) (n : ℕ) (x : ℝ) :
    0 ≤ stepProfile w n x
```

### ProfileLimit.aestronglyMeasurable

lemma; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:62)

```lean
lemma ProfileLimit.aestronglyMeasurable {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) : AEStronglyMeasurable f profileMeasure
```

### ProfileLimit.ae_pos

lemma; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:68)

```lean
lemma ProfileLimit.ae_pos {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) : ∀ᵐ x ∂profileMeasure, 0 < f x
```

### ProfileLimit.ae_nonneg

lemma; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:73)

```lean
lemma ProfileLimit.ae_nonneg {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) : ∀ᵐ x ∂profileMeasure, 0 ≤ f x
```

### ProfileLimit.integrable

lemma; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:80)

`L¹` convergence to a measurable limit forces its integrability.  The
finiteness is obtained from an actual finite error term, not from normalization.

```lean
lemma ProfileLimit.integrable {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) : Integrable f profileMeasure
```

### ProfileLimit.tendsto_integral_abs_sub

lemma; [source line 97](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:97)

The real integral form of precisely the existing extended `L¹` error.
All errors are integrable, so no totalized integral is being used.

```lean
lemma ProfileLimit.tendsto_integral_abs_sub {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) :
    Tendsto (fun n => ∫ x, |stepProfile w n x - f x| ∂profileMeasure) atTop (𝓝 0)
```

### profileCell_subset

lemma; [source line 109](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:109)

```lean
lemma profileCell_subset (n : ℕ) (i : Fin n) :
    profileCell n i ⊆ Ioo (0 : ℝ) 1
```

### stepProfile_eq_of_mem_Ioc

lemma; [source line 118](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:118)

Exact pointwise value on the paper's half-open cell, including its right endpoint.

```lean
lemma stepProfile_eq_of_mem_Ioc (w : WeightArray) (n : ℕ) (i : Fin n) {x : ℝ}
    (hx : x ∈ Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)) :
    stepProfile w n x = (w n).rate i
```

### stepProfile_eq_on_cell

lemma; [source line 138](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:138)

```lean
lemma stepProfile_eq_on_cell (w : WeightArray) (n : ℕ) (i : Fin n) {x : ℝ}
    (hx : x ∈ profileCell n i) : stepProfile w n x = (w n).rate i
```

### profileMeasure_cell

lemma; [source line 142](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:142)

```lean
lemma profileMeasure_cell (n : ℕ) (i : Fin n) :
    profileMeasure (profileCell n i) = ENNReal.ofReal (1 / (n : ℝ))
```

### integral_stepProfile_cell

lemma; [source line 152](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:152)

The normalized weight is exactly the mass of its actual profile cell.

```lean
lemma integral_stepProfile_cell (w : WeightArray) (n : ℕ) (i : Fin n) :
    ∫ x in profileCell n i, stepProfile w n x ∂profileMeasure = (w n).rate i / n
```

### ProfileLimit.rate_div_tendsto_zero

theorem; [source line 167](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:167)

Equation `eq:max-weight`, first in its stronger arbitrary-cell form.
The chosen label may depend on the row without any consistency condition.

```lean
theorem ProfileLimit.rate_div_tendsto_zero {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (i : ∀ n, Fin (n + 1)) :
    Tendsto (fun n => (w (n + 1)).rate (i n) / (n + 1 : ℕ)) atTop (𝓝 0)
```

### rowMaxRate

def; [source line 183](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:183)

Maximum rate in positive row `n+1`; the row shift removes only the
irrelevant empty initial row of the triangular array.

```lean
def rowMaxRate (w : WeightArray) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (n + 1) => (w (n + 1)).rate i)
```

### rate_le_rowMaxRate

lemma; [source line 186](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:186)

```lean
lemma rate_le_rowMaxRate (w : WeightArray) (n : ℕ) (i : Fin (n + 1)) :
    (w (n + 1)).rate i ≤ rowMaxRate w n
```

### ProfileLimit.max_weight_div_tendsto_zero

theorem; [source line 192](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:192)

The largest normalized rate tends to zero under precisely Assumption 1.1,
as asserted in `fixed_points.tex`, Section 3, equation `eq:max-weight`.

```lean
theorem ProfileLimit.max_weight_div_tendsto_zero {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) :
    Tendsto (fun n => rowMaxRate w n / (n + 1 : ℕ)) atTop (𝓝 0)
```

### ProfileAssumption.max_weight_div_tendsto_zero

theorem; [source line 203](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:203)

```lean
theorem ProfileAssumption.max_weight_div_tendsto_zero {w : WeightArray}
    (h : ProfileAssumption w) :
    Tendsto (fun n => rowMaxRate w n / (n + 1 : ℕ)) atTop (𝓝 0)
```

### ProfileLimit.uniform_profileD

theorem; [source line 211](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:211)

The deterministic remaining-rate transform converges uniformly on all
nonnegative times directly from Assumption 1.1.

```lean
theorem ProfileLimit.uniform_profileD {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) :
    TendstoUniformlyOn (fun n => profileD profileMeasure (stepProfile w n))
      (profileD profileMeasure f) atTop (Ici 0)
```

### ProfileLimit.uniform_profileF

theorem; [source line 221](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:221)

The deterministic arrival transform converges uniformly on every finite
time interval directly from Assumption 1.1.

```lean
theorem ProfileLimit.uniform_profileF {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (T : ℝ) :
    TendstoUniformlyOn (fun n => profileF profileMeasure (stepProfile w n))
      (profileF profileMeasure f) atTop (Icc 0 T)
```

### exists_profile_cell

lemma; [source line 231](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:231)

The paper's half-open cells cover their stated domain.  This also checks
that the step-profile representation has no omitted positive-measure points.

```lean
lemma exists_profile_cell {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ∃ i : Fin n, x ∈ Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)
```

### section3UnitWeights

def; [source line 255](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:255)

Concrete normalized example: every rate is one in every row.

```lean
def section3UnitWeights : WeightArray := fun _ =>
  ⟨fun _ => 1, fun _ => zero_lt_one⟩
```

### section3UnitWeights_normalized

lemma; [source line 258](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:258)

```lean
lemma section3UnitWeights_normalized : NormalizedWeights section3UnitWeights
```

### section3UnitWeights_profileLimit

theorem; [source line 264](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Profile.lean:264)

The profile hypothesis has an explicit inhabitant.  The constant-one
profile of the constant-one weights converges exactly, apart from row zero.

```lean
theorem section3UnitWeights_profileLimit :
    ProfileLimit section3UnitWeights (fun _ => 1)
```


## Luce/Section3Quantile.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Luce
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
```

### integral_pos_of_ae_pos

lemma; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:24)

```lean
private lemma integral_pos_of_ae_pos [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : Integrable g μ) (hpos : ∀ᵐ x ∂μ, 0 < g x) :
    0 < ∫ x, g x ∂μ
```

### profileD_pos

theorem; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:38)

Strict positivity of the limiting remaining rate at every finite
nonnegative time; this supplies the interior denominator bound.

```lean
theorem profileD_pos [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {t : ℝ} (ht : 0 ≤ t) :
    0 < profileD μ f t
```

### profileF_zero

theorem; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:46)

The lower endpoint of the distribution transform is exactly zero.

```lean
@[simp] theorem profileF_zero [IsProbabilityMeasure μ] (f : Ω → ℝ) :
    profileF μ f 0 = 0
```

### strictMonoOn_profileF

theorem; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:52)

The distribution transform is strictly increasing, as asserted before
the definition of the inverse time `t_x` in the manuscript.

```lean
theorem strictMonoOn_profileF [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    StrictMonoOn (profileF μ f) (Ici 0)
```

### profileF_lt_one

theorem; [source line 70](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:70)

At every finite time the distribution transform remains below one.

```lean
theorem profileF_lt_one [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {t : ℝ} (ht : 0 ≤ t) :
    profileF μ f t < 1
```

### profileF_nonneg

theorem; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:80)

```lean
theorem profileF_nonneg [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ profileF μ f t
```

### tendsto_profileF_atTop

theorem; [source line 89](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:89)

Dominated convergence identifies the upper endpoint of the limiting
distribution transform, using positivity rather than a lower bound on `f`.

```lean
theorem tendsto_profileF_atTop [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    Tendsto (profileF μ f) atTop (𝓝 1)
```

### exists_profileF_eq

theorem; [source line 116](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:116)

Every interior spatial coordinate, including zero, has a nonnegative
inverse time. This establishes existence before defining or using the inverse.

```lean
theorem exists_profileF_eq [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {x : ℝ}
    (hx : x ∈ Ico 0 1) : ∃ t ∈ Ici (0 : ℝ), profileF μ f t = x
```

### profileQuantile

def; [source line 132](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:132)

The inverse used for the paper's `t_x`: standard `invFunOn` restricts
the time variable to the nonnegative half-line. Its values outside the
distribution's image are irrelevant; no inverse property is built in.

```lean
def profileQuantile (μ : Measure Ω) (f : Ω → ℝ) (x : ℝ) : ℝ :=
  Function.invFunOn (profileF μ f) (Ici 0) x
```

### profileQuantile_nonneg

theorem; [source line 135](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:135)

```lean
theorem profileQuantile_nonneg [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {x : ℝ}
    (hx : x ∈ Ico 0 1) : 0 ≤ profileQuantile μ f x
```

### profileF_profileQuantile

theorem; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:141)

The inverse is an actual right inverse on the full interval `[0,1)`.

```lean
theorem profileF_profileQuantile [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {x : ℝ}
    (hx : x ∈ Ico 0 1) : profileF μ f (profileQuantile μ f x) = x
```

### profileQuantile_profileF

theorem; [source line 147](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:147)

Strict increase also proves uniqueness of every nonnegative inverse time.

```lean
theorem profileQuantile_profileF [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {t : ℝ} (ht : 0 ≤ t) :
    profileQuantile μ f (profileF μ f t) = t
```

### profileQuantile_zero

theorem; [source line 153](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:153)

The inverse endpoint convention required in Section 3 is forced by `F 0 = 0`.

```lean
theorem profileQuantile_zero [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    profileQuantile μ f 0 = 0
```

### strictMonoOn_profileQuantile

theorem; [source line 158](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:158)

```lean
theorem strictMonoOn_profileQuantile [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    StrictMonoOn (profileQuantile μ f) (Ico 0 1)
```

### continuousOn_profileQuantile

theorem; [source line 171](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:171)

The inverse is continuous on `[0,1)`, including at zero. No regularity
of the original profile beyond integrability and positivity is imposed.

```lean
theorem continuousOn_profileQuantile [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    ContinuousOn (profileQuantile μ f) (Ico 0 1)
```

### uniform_profile_inverse_modulus

theorem; [source line 195](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Quantile.lean:195)

A uniform inversion modulus on an interior spatial interval. The time
cutoff has a strict CDF margin beyond `α`, so an empirical CDF error smaller
than `δ` also confines all the relevant order statistics to this time cutoff.
This is the quantitative step behind `eq:uniform-quantile`.

```lean
theorem uniform_profile_inverse_modulus [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {α ε : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ T δ : ℝ, 0 ≤ T ∧ 0 < δ ∧ α + δ < profileF μ f T ∧
      ∀ x ∈ Icc (0 : ℝ) α, ∀ t ∈ Icc (0 : ℝ) T,
        |profileF μ f t - x| < δ → |t - profileQuantile μ f x| < ε
```


## Luce/Section3Race.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Race.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### section3_sum_rates

lemma; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Race.lean:21)

Normalization is a standing manuscript hypothesis, not a consequence
silently inserted into `ProfileLimit`.

```lean
private lemma section3_sum_rates {w : WeightArray} (hnorm : NormalizedWeights w)
    (n : ℕ) : ∑ i, (w (n + 1)).rate i = ((n + 1 : ℕ) : ℝ)
```

### ProfileLimit.integral_eq_one

theorem; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Race.lean:31)

The unit-mass conclusion stated in Assumption 1.1 (line 228) follows
from normalization and L¹ convergence; it is not a new profile hypothesis.

```lean
theorem ProfileLimit.integral_eq_one {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) :
    (∫ x, f x ∂profileMeasure) = 1
```

### section3_uniform_arrival

theorem; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Race.lean:54)

Equation `eq:uniform-race`, arrival part. Even normalization is
unnecessary for this part; only the stated L¹ profile assumption is used.

```lean
theorem section3_uniform_arrival
    (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalArrival clocks t - profileF profileMeasure f t|})
      atTop (𝓝 0)
```

### section3_uniform_remaining

theorem; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Race.lean:69)

Equation `eq:uniform-race`, with exactly the paper's weak survival
process, including at zero and at arrival times.

```lean
theorem section3_uniform_remaining
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalRemainingGe (w (n + 1)) clocks t -
          profileD profileMeasure f t|}) atTop (𝓝 0)
```

### section3_uniform_race

theorem; [source line 86](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Race.lean:86)

The two uniform process limits in Lemma 3.1 (lines 687–693).
The later quantile and denominator conclusions are separate obligations.

```lean
theorem section3_uniform_race
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (T : ℝ) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalArrival clocks t - profileF profileMeasure f t|})
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalRemainingGe (w (n + 1)) clocks t -
          profileD profileMeasure f t|}) atTop (𝓝 0))
```

### section3_uniform_race_of_independent

theorem; [source line 102](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Race.lean:102)

Uniform bad-event estimates transfer to any row spaces having the
prescribed independent exponential clocks. No measurability of an uncountable
supremum is assumed: the outer-measure preimage inequality suffices.

```lean
theorem section3_uniform_race_of_independent
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Fin (n + 1) → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w (n + 1)).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) (T : ℝ) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalArrival (fun i => E n i ω) t - profileF profileMeasure f t|})
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalRemainingGe (w (n + 1)) (fun i => E n i ω) t -
          profileD profileMeasure f t|}) atTop (𝓝 0))
```

### section3_uniform_race_general

theorem; [source line 136](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Race.lean:136)

Equation `eq:uniform-race` with the manuscript's original row index,
on arbitrary probability spaces. The zero row is removed by a proved filter
shift, so no hidden positive-row assumption occurs in the statement.

```lean
theorem section3_uniform_race_general
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) (T : ℝ) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalArrival (fun i => E n i ω) t - profileF profileMeasure f t|})
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ t ∈ Icc 0 T,
        ε ≤ |empiricalRemainingGe (w n) (fun i => E n i ω) t -
          profileD profileMeasure f t|}) atTop (𝓝 0))
```


## Luce/Section3RaceDrawLaw.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceDrawLaw.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace Luce
```

### strictMono_draw_clocks

lemma; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceDrawLaw.lean:18)

```lean
lemma strictMono_draw_clocks {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) :
    StrictMono (fun k => clocks (drawPermutation clocks hinj k))
```

### drawPermutation_eq_iff_strictMono

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceDrawLaw.lean:30)

The sorted draw permutation is uniquely characterized by increasing
clock times. The finite order comparison proves uniqueness at every index.

```lean
theorem drawPermutation_eq_iff_strictMono {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (π : Equiv.Perm (Fin n)) :
    drawPermutation clocks hinj = π ↔ StrictMono (fun k => clocks (π k))
```

### measurableSet_injective_clocks

lemma; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceDrawLaw.lean:53)

```lean
lemma measurableSet_injective_clocks (n : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ | Function.Injective clocks}
```

### measurable_raceDraw

theorem; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceDrawLaw.lean:69)

The full draw order is measurable into the discrete finite permutation
space, including the exceptional tied-clock configurations.

```lean
theorem measurable_raceDraw (n : ℕ) :
    @Measurable (Fin n → ℝ) (Equiv.Perm (Fin n)) inferInstance ⊤ raceDraw
```

### raceDraw_mass

theorem; [source line 97](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceDrawLaw.lean:97)

The total measurable draw permutation has the exact full Luce law.

```lean
theorem raceDraw_mass {n : ℕ} (w : Weights n) (π : Equiv.Perm (Fin n)) :
    (exponentialRace w).real {clocks | raceDraw clocks = π} = w.mass π
```


## Luce/Section3RaceLaw.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal
namespace Luce
```

### exponentialRace_residual_measure

theorem; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:25)

Product memorylessness: after every clock survives a deterministic time,
subtracting that time gives the original independent race, with its exact
unnormalized survival probability. No conditional law is assumed.

```lean
theorem exponentialRace_residual_measure {n : ℕ} (w : Weights n)
    {s : ℝ} (hs : 0 ≤ s) :
    ((exponentialRace w).restrict (Set.univ.pi (fun _ => Ioi s))).map
        (fun clocks i => clocks i - s) =
      ENNReal.ofReal (Real.exp (-(w.total Finset.univ * s))) • exponentialRace w
```

### measurableSet_strictMono_clocks

lemma; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:53)

```lean
lemma measurableSet_strictMono_clocks (n : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ | StrictMono clocks}
```

### strictMono_sub_const_iff

lemma; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:60)

```lean
lemma strictMono_sub_const_iff {n : ℕ} (clocks : Fin n → ℝ) (s : ℝ) :
    StrictMono (fun i => clocks i - s) ↔ StrictMono clocks
```

### exponentialRace_surviving_order

theorem; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:69)

The sorted event is invariant under subtracting a common time, while
the survival event contributes exactly the product exponential factor.

```lean
theorem exponentialRace_surviving_order {n : ℕ} (w : Weights n)
    {s : ℝ} (hs : 0 ≤ s) :
    exponentialRace w {clocks | (∀ i, s < clocks i) ∧ StrictMono clocks} =
      ENNReal.ofReal (Real.exp (-(w.total Finset.univ * s))) *
        exponentialRace w {clocks | StrictMono clocks}
```

### exponentialRace_event_disintegrate

theorem; [source line 90](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:90)

The distinguished-clock disintegration specialized to an arbitrary
measurable event; this is derived by integrating its indicator.

```lean
theorem exponentialRace_event_disintegrate {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (A : Set (ℝ × (Fin n → ℝ))) (hA : MeasurableSet A) :
    exponentialRace w {clocks | (clocks i, fun j => clocks (i.succAbove j)) ∈ A} =
      ∫⁻ t, exponentialPDF (w.rate i) t *
        backgroundRace w i {background | (t, background) ∈ A}
```

### backgroundRace_zero

lemma; [source line 109](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:109)

```lean
lemma backgroundRace_zero {n : ℕ} (w : Weights (n + 1)) :
    backgroundRace w 0 = exponentialRace (w.removeFirst 0)
```

### measurableSet_first_before_background

lemma; [source line 115](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:115)

```lean
lemma measurableSet_first_before_background (n : ℕ) :
    MeasurableSet {z : ℝ × (Fin n → ℝ) | ∀ j, z.1 < z.2 j}
```

### strictMono_clocks_iff

lemma; [source line 121](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:121)

```lean
lemma strictMono_clocks_iff {n : ℕ} (clocks : Fin (n + 1) → ℝ) :
    StrictMono clocks ↔
      (∀ j : Fin n, clocks 0 < clocks j.succ) ∧ StrictMono (fun j : Fin n => clocks j.succ)
```

### exponentialRace_order_disintegrate

theorem; [source line 132](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:132)

The first sorted clock can be exposed before all remaining clocks,
retaining their exact ordered-event probability.

```lean
theorem exponentialRace_order_disintegrate {n : ℕ} (w : Weights (n + 1)) :
    exponentialRace w {clocks | StrictMono clocks} =
      ∫⁻ t, exponentialPDF (w.rate 0) t *
        exponentialRace (w.removeFirst 0)
          {background | (∀ j, t < background j) ∧ StrictMono background}
```

### first_clock_event_iff

lemma; [source line 143](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:143)

```lean
lemma first_clock_event_iff {n : ℕ} (clocks : Fin (n + 1) → ℝ)
    (hinj : Function.Injective clocks) :
    (∀ j : Fin n, clocks 0 < clocks j.succ) ↔ raceRank clocks 0 = 1
```

### exponentialRace_first_clock_probability

theorem; [source line 160](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:160)

The unrestricted order of the background drops out of the first-choice
probability. This identity uses the already proved exact first-choice law.

```lean
theorem exponentialRace_first_clock_probability {n : ℕ} (w : Weights (n + 1)) :
    exponentialRace w {clocks | ∀ j : Fin n, clocks 0 < clocks j.succ} =
      ENNReal.ofReal (w.rate 0 / w.total Finset.univ)
```

### exponentialRace_all_survive

theorem; [source line 170](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:170)

Exact probability that every independent clock survives a fixed time.

```lean
theorem exponentialRace_all_survive {n : ℕ} (w : Weights n) {s : ℝ} (hs : 0 ≤ s) :
    exponentialRace w {clocks | ∀ i, s < clocks i} =
      ENNReal.ofReal (Real.exp (-(w.total Finset.univ * s)))
```

### exponentialRace_order_recursion

theorem; [source line 187](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:187)

The sorted-event probability satisfies exactly the same first-draw
recursion as the Luce mass. The factorization follows from product
memorylessness and integration, without assuming conditional independence.

```lean
theorem exponentialRace_order_recursion {n : ℕ} (w : Weights (n + 1)) :
    exponentialRace w {clocks | StrictMono clocks} =
      ENNReal.ofReal (w.rate 0 / w.total Finset.univ) *
        exponentialRace (w.removeFirst 0) {clocks | StrictMono clocks}
```

### exponentialRace_identity_order_probability

theorem; [source line 218](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:218)

The increasing-label order has exactly its Luce product mass, by the
first-clock recursion. The induction begins with the genuinely empty race.

```lean
theorem exponentialRace_identity_order_probability {n : ℕ} (w : Weights n) :
    exponentialRace w {clocks | StrictMono clocks} =
      ENNReal.ofReal (w.mass (Equiv.refl (Fin n)))
```

### exponentialRace_order_probability

theorem; [source line 241](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RaceLaw.lean:241)

The complete exponential-race representation of `eq:luce-law`.
The event records the entire draw order, rather than merely its first draw.
No normalization is needed because the Luce law is invariant under scaling.

```lean
theorem exponentialRace_order_probability {n : ℕ} (w : Weights n)
    (π : Equiv.Perm (Fin n)) :
    (exponentialRace w).real {clocks | StrictMono (fun r => clocks (π r))} =
      w.mass π
```


## Luce/Section3RemainingWeight.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RemainingWeight.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Luce
```

### section3_uniform_remaining_weight_general

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section3RemainingWeight.lean:20)

Source Lemma 3.1, equation `eq:uniform-denominator`: the remaining-set
weight converges uniformly to `D(t(k/n))` on every interior window.

```lean
theorem section3_uniform_remaining_weight_general
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (E : ∀ n, Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
        ε ≤ |(w n).total (remaining (raceDraw (fun i => E n i ω)) k) / n -
          profileD profileMeasure f
            (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / n))|})
      atTop (𝓝 0)
```


## Luce/Section3Replacement.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Replacement.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### probability_error_le_bad_add_integral

lemma; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Replacement.lean:21)

Markov's inequality with an exceptional event. The error itself need
not be measurable because the estimate uses outer probability.

```lean
lemma probability_error_le_bad_add_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (bad : Set Ω)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hY : Integrable Y μ)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hbound : ∀ ω, ω ∉ bad → |X ω| ≤ C * Y ω) :
    μ.real {ω | ε < |X ω|} ≤ μ.real bad + (C / ε) * ∫ ω, Y ω ∂μ
```

### integrable_normalized_clockBand

lemma; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Replacement.lean:44)

```lean
lemma integrable_normalized_clockBand {n : ℕ} (w : Weights (n + 1))
    (s : Finset (Fin (n + 1))) (t : Fin (n + 1) → ℝ) (δ : ℝ) :
    Integrable (fun E =>
      (∑ i ∈ s, w.rate i * clockBand (t i) δ (E i)) / (n + 1 : ℕ))
      (exponentialRace w)
```

### probability_survival_replacement_le

theorem; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Replacement.lean:60)

A quantitative version of the replacement argument: the error
probability is bounded by the quantile error probability plus a constant
times the band width. The estimates are uniform in n and in all rates.

```lean
theorem probability_survival_replacement_le {n : ℕ} (w : Weights (n + 1))
    (s : Finset (Fin (n + 1))) (c t : Fin (n + 1) → ℝ)
    (τ : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) {C u δ ε : ℝ}
    (hC : 0 ≤ C) (hc : ∀ i ∈ s, |c i| ≤ C) (hu : 0 < u)
    (ht : ∀ i ∈ s, u ≤ t i) (hδ : 0 ≤ δ) (hδu : δ ≤ u / 2) (hε : 0 < ε) :
    (exponentialRace w).real {E | ε <
      |((∑ i ∈ s, c i * w.rate i * survivalGe (τ E i) (E i)) -
        (∑ i ∈ s, c i * w.rate i * survivalGe (t i) (E i))) / (n + 1 : ℕ)|} ≤
      (exponentialRace w).real {E | ∃ i ∈ s, δ < |τ E i - t i|} +
        (C / ε) * (8 * δ / (u / 2) ^ 2)
```

### survival_replacement_converges

theorem; [source line 101](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Replacement.lean:101)

The full stochastic replacement step on any fixed positive cutoff.
Quantile convergence is supplied explicitly; the shrinking-band probability
bound is proved from the actual exponential law above.

```lean
theorem survival_replacement_converges
    (w : ∀ n, Weights (n + 1)) (s : ∀ n, Finset (Fin (n + 1)))
    (c t : ∀ n, Fin (n + 1) → ℝ)
    (τ : ∀ n, (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) {C u : ℝ}
    (hC : 0 ≤ C) (hc : ∀ n i, i ∈ s n → |c n i| ≤ C)
    (hu : 0 < u) (ht : ∀ n i, i ∈ s n → u ≤ t n i)
    (hquantile : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => (exponentialRace (w n)).real
      {E | ∃ i ∈ s n, δ < |τ n E i - t n i|}) atTop (𝓝 0)) :
    ConvergesInProbability (fun n => exponentialRace (w n))
      (fun n E =>
        ((∑ i ∈ s n, c n i * (w n).rate i * survivalGe (τ n E i) (E i)) -
          (∑ i ∈ s n, c n i * (w n).rate i * survivalGe (t n i) (E i))) /
            (n + 1 : ℕ)) 0
```

### deterministic_survival_fluctuation_converges

theorem; [source line 135](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Replacement.lean:135)

The deterministic-time sum is asymptotic in probability to its exact
expectation on a fixed positive cutoff (lines 776–780).

```lean
theorem deterministic_survival_fluctuation_converges
    (w : ∀ n, Weights (n + 1)) (s : ∀ n, Finset (Fin (n + 1)))
    (c t : ∀ n, Fin (n + 1) → ℝ) {C u : ℝ}
    (hc : ∀ n i, i ∈ s n → |c n i| ≤ C)
    (hu : 0 < u) (ht : ∀ n i, i ∈ s n → u ≤ t n i) :
    ConvergesInProbability (fun n => exponentialRace (w n))
      (fun n E =>
        (∑ i ∈ s n, c n i * (w n).rate i * survivalGe (t n i) (E i)) /
            (n + 1 : ℕ) -
          (∑ i ∈ s n, c n i * rateKernel (t n i) ((w n).rate i)) / (n + 1 : ℕ)) 0
```


## Luce/Section3Representations.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Representations.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce
```

### interiorDensityMeasure_eq_closed

theorem; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Representations.lean:16)

Deleting the zero endpoint does not change the manuscript intensity.

```lean
theorem interiorDensityMeasure_eq_closed (f : ℝ → ℝ) (α : ℝ) :
    interiorDensityMeasure f α =
      (volume.restrict (Icc (0 : ℝ) α)).withDensity
        (fun x => ENNReal.ofReal (profileDiagonal f x))
```

### interior_integral_eq_closed

theorem; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Representations.lean:26)

The signed limiting integral agrees with the literal closed-interval
Lebesgue integral, including zero and empty intervals.

```lean
theorem interior_integral_eq_closed (f g : ℝ → ℝ) (α : ℝ) :
    (∫ x in Ioc (0 : ℝ) α, g x * profileDiagonal f x) =
      ∫ x in Icc (0 : ℝ) α, g x * profileDiagonal f x
```

### interiorFixedPoints_realMeasure

theorem; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Representations.lean:34)

Forgetting the compact-interval subtype recovers exactly the paper's
real-line Dirac sum, with its one-based labels and inverse-rank convention.

```lean
theorem interiorFixedPoints_realMeasure {n : ℕ} (α : ℝ)
    (π : Equiv.Perm (Fin n)) :
    ((interiorFixedPoints α π).toFiniteMeasure : Measure (Icc (0 : ℝ) 1)).map
      Subtype.val = ∑ k : Fin n,
        if ((k.val : ℝ) + 1) / n ≤ α ∧ π.symm k = k then
          Measure.dirac (((k.val : ℝ) + 1) / n) else 0
```


## Luce/Section3Survival.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Survival.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace Luce
```

### initialRateMass_mono

lemma; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Survival.lean:20)

```lean
lemma initialRateMass_mono (w : WeightArray) (n : ℕ) :
    Monotone (initialRateMass w n)
```

### normalized_sum_cutoff_error_le

lemma; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Survival.lean:29)

Quantitative bound for discarding labels at or before η.

```lean
lemma normalized_sum_cutoff_error_le (w : WeightArray) (n : ℕ)
    (s : Finset (Fin (n + 1))) (X : Fin (n + 1) → ℝ) {η C : ℝ}
    (hC : 0 ≤ C) (hX : ∀ i ∈ s, |X i| ≤ C * (w (n + 1)).rate i) :
    |(∑ i ∈ s, X i) / (n + 1 : ℕ) -
      (∑ i ∈ s.filter (fun i => η < ((i.val : ℝ) + 1) / (n + 1 : ℕ)), X i) /
        (n + 1 : ℕ)| ≤ C * initialRateMass w n η
```

### survivalGe_abs_sub_le_one

lemma; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Survival.lean:62)

```lean
lemma survivalGe_abs_sub_le_one (s t x : ℝ) : |survivalGe s x - survivalGe t x| ≤ 1
```

### profileQuantile_pos_of_pos

lemma; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Survival.lean:68)

```lean
lemma profileQuantile_pos_of_pos {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    0 < profileQuantile profileMeasure f η
```

### section3_survival_replacement

theorem; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Survival.lean:78)

Equation (replacement of survival indicators) for all selected interior
labels, under the actual profile hypothesis. The set s may be the full
interval k/n ≤ α or any of its subsets.

```lean
theorem section3_survival_replacement (w : WeightArray) (f : ℝ → ℝ)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (s : ∀ n, Finset (Fin (n + 1))) (c : ∀ n, Fin (n + 1) → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hs : ∀ n i, i ∈ s n → ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α)
    (hc : ∀ n i, i ∈ s n → |c n i| ≤ C) :
    ConvergesInProbability (fun n => exponentialRace (w (n + 1)))
      (fun n E =>
        ((∑ i ∈ s n, c n i * (w (n + 1)).rate i * survivalGe (orderTime E i) (E i)) -
          (∑ i ∈ s n, c n i * (w (n + 1)).rate i *
            survivalGe (profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ))) (E i))) /
          (n + 1 : ℕ)) 0
```

### section3_survival_fluctuation

theorem; [source line 150](D:/princeton/Research/Lean/Lean_luce/Luce/Section3Survival.lean:150)

The full interior deterministic-survival fluctuation, with its exact
expectation subtracted. Small times are handled by the profile's initial
mass estimate, so no time cutoff is retained in the statement.

```lean
theorem section3_survival_fluctuation (w : WeightArray) (f : ℝ → ℝ)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (s : ∀ n, Finset (Fin (n + 1))) (c : ∀ n, Fin (n + 1) → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hs : ∀ n i, i ∈ s n → ((i.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α)
    (hc : ∀ n i, i ∈ s n → |c n i| ≤ C) :
    ConvergesInProbability (fun n => exponentialRace (w (n + 1)))
      (fun n E =>
        (∑ i ∈ s n, c n i * (w (n + 1)).rate i *
          survivalGe (profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ))) (E i)) /
            (n + 1 : ℕ) -
          (∑ i ∈ s n, c n i *
            rateKernel (profileQuantile profileMeasure f (((i.val : ℝ) + 1) / (n + 1 : ℕ)))
              ((w (n + 1)).rate i)) / (n + 1 : ℕ)) 0
```


## Luce/Section4.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4.lean)

No declarations; imports or audit commands only.


## Luce/Section4Approximation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Approximation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal
namespace Luce
```

### tendsto_of_terminal_approximation

theorem; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Approximation.lean:18)

Scalar converging-together lemma, with every real-limsup boundedness
condition stated. In the application p is an actual probability.

```lean
theorem tendsto_of_terminal_approximation
    (u : ℕ → ℝ) (v : ℝ → ℕ → ℝ) (a : ℝ → ℝ) (p : ℝ → ℕ → ℝ) (L : ℝ)
    (hp : ∀ α, IsBoundedUnder (· ≤ ·) atTop (p α))
    (htail : Tendsto (fun α => limsup (p α) atTop) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (ha : Tendsto a (𝓝[<] (1 : ℝ)) (𝓝 L))
    (hv : ∀ α, α < 1 → Tendsto (v α) atTop (𝓝 (a α)))
    (happrox : ∀ α, α < 1 → ∀ n, |u n - v α n| ≤ p α n) :
    Tendsto u atTop (𝓝 L)
```

### abs_integral_sub_le_probability

lemma; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Approximation.lean:46)

An integrable test taking values in [0,1] changes in expectation by at
most the probability of the event on which it changes.

```lean
lemma abs_integral_sub_le_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F G : Ω → ℝ}
    (hF : Integrable F P) (hG : Integrable G P)
    (hFb : ∀ ω, F ω ∈ Icc (0 : ℝ) 1) (hGb : ∀ ω, G ω ∈ Icc (0 : ℝ) 1)
    {bad : Set Ω} (hbad : MeasurableSet bad)
    (heq : ∀ᵐ ω ∂P, ω ∉ bad → F ω = G ω) :
    |(∫ ω, F ω ∂P) - ∫ ω, G ω ∂P| ≤ P.real bad
```

### fixedPoints_eq_interior_of_tail_zero

theorem; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Approximation.lean:66)

Every missing atom would be a terminal fixed point, so a zero terminal
count gives equality of the actual finite measures, not just their masses.

```lean
theorem fixedPoints_eq_interior_of_tail_zero {n : ℕ} (e : Fin n → ℝ)
    (hinj : Function.Injective e) (α : ℝ) (hz : tailFixedPointCount e α = 0) :
    fixedPoints (raceDraw e) = interiorFixedPoints α (raceDraw e)
```

### measurable_interiorFixedPoints_race

lemma; [source line 90](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Approximation.lean:90)

```lean
lemma measurable_interiorFixedPoints_race {n : ℕ} (w : Weights n) (α : ℝ) :
    Measurable (fun e : Fin n → ℝ => interiorFixedPoints α (raceDraw e))
```

### section4_laplace_cutoff_error

theorem; [source line 99](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Approximation.lean:99)

The Laplace-test cutoff error is bounded by the exact tail probability.

```lean
theorem section4_laplace_cutoff_error {n : ℕ} (w : Weights n) (α : ℝ)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
    |(∫ e, pointLaplace (fun x => (g x : ℝ)) (fixedPoints (raceDraw e)) ∂exponentialRace w) -
      ∫ e, pointLaplace (fun x => (g x : ℝ)) (interiorFixedPoints α (raceDraw e))
        ∂exponentialRace w| ≤
      (exponentialRace w).real {e | 0 < tailFixedPointCount e α}
```


## Luce/Section4Compensator.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Compensator.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology BoundedContinuousFunction
namespace Luce
```

### FiniteAdaptedBernoulli.integral_probability_eq

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Compensator.lean:19)

Integrating a finite conditional probability recovers the observation's
expectation; clipping the conditional expectation changes only a null set.

```lean
theorem FiniteAdaptedBernoulli.integral_probability_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (B : FiniteAdaptedBernoulli P n) (k : Fin n) :
    (∫ ω, B.probability k ω ∂P) = ∫ ω, B.observationReal k ω ∂P
```

### FiniteAdaptedBernoulli.integral_predictable_eq_observed

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Compensator.lean:28)

Spatially weighted observed and predictable measures have identical
expectations, with integrability supplied by the finite row.

```lean
theorem FiniteAdaptedBernoulli.integral_predictable_eq_observed
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    (B : FiniteAdaptedBernoulli P n) (x : Fin n → X) (g : X → ℝ)
    (hg : Measurable g) :
    (∫ ω, ∫ y, g y ∂(B.predictableMeasure x ω : Measure X) ∂P) =
      ∫ ω, ∫ y, g y ∂((B.pointMeasure x ω).toFiniteMeasure : Measure X) ∂P
```

### section4_interior_test_expectation_lower

theorem; [source line 49](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Compensator.lean:49)

The limiting intensity of a nonnegative continuous test is bounded by
the limsup of its actual observed expectations. Only the upper boundedness
needed for a real limsup is assumed here; endpoint estimates discharge it
when the test is supported in the terminal interval.

```lean
theorem section4_interior_test_expectation_lower
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) (hg : ∀ x, 0 ≤ g x)
    (hbounded : IsBoundedUnder (· ≤ ·) atTop (fun n => ∫ e,
      ∫ y, g y ∂((interiorFixedPoints α (raceDraw e)).toFiniteMeasure :
        Measure (Icc (0 : ℝ) 1)) ∂exponentialRace (w n))) :
    (∫ y, g y ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1))) ≤
      limsup (fun n => ∫ e, ∫ y, g y
        ∂((interiorFixedPoints α (raceDraw e)).toFiniteMeasure : Measure (Icc (0 : ℝ) 1))
        ∂exponentialRace (w n)) atTop
```


## Luce/Section4Count.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Count.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open Classical
namespace Luce
```

### fixedPoints

abbrev; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Count.lean:20)

The full process is the existing literal Dirac sum with cutoff one.

```lean
abbrev fixedPoints {n : ℕ} (π : Equiv.Perm (Fin n)) := interiorFixedPoints 1 π
```

### observedPointMeasure_count

theorem; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Count.lean:23)

Evaluation of an observed point measure is the exact selected-label count.

```lean
theorem observedPointMeasure_count {X : Type*} [MeasurableSpace X] {n : ℕ}
    (x : Fin n → X) (b : Fin n → Bool) {A : Set X} (hA : MeasurableSet A) :
    (observedPointMeasure x b).count A =
      (Finset.univ.filter fun k => b k = true ∧ x k ∈ A).card
```

### raceDraw_fixed_iff_rankOf

lemma; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Count.lean:40)

The inverse of the sorted draw permutation has exactly the clock rank.

```lean
lemma raceDraw_fixed_iff_rankOf {n : ℕ} (e : Fin n → ℝ)
    (hinj : Function.Injective e) (k : Fin n) :
    (raceDraw e).symm k = k ↔ rankOf e k = k.val + 1
```

### fixedPoints_tail_count

theorem; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Count.lean:50)

The source's `Ξ_n((α,1])` is exactly the existing spatial tail count.
No rounding or off-by-one error is absorbed in an inequality.

```lean
theorem fixedPoints_tail_count {n : ℕ} (e : Fin n → ℝ)
    (hinj : Function.Injective e) (α : ℝ) :
    (fixedPoints (raceDraw e)).count {x | α < x.val} = tailFixedPointCount e α
```

### fixedPoints_tail_count_ae

theorem; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Count.lean:69)

The exact process-count bridge holds almost surely under the model's
clock law; distinctness is proved, not supplied as a hypothesis.

```lean
theorem fixedPoints_tail_count_ae {n : ℕ} (w : Weights n) (α : ℝ) :
    (fun e => (fixedPoints (raceDraw e)).count {x | α < x.val}) =ᵐ[exponentialRace w]
      (fun e => tailFixedPointCount e α)
```

### section4_point_measure_tail_tightness

theorem; [source line 77](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Count.lean:77)

Equation `eq:tail-tightness` for evaluation of the actual random finite
point measure, now connected exactly to the previously proved count theorem.

```lean
theorem section4_point_measure_tail_tightness (w : WeightArray)
    (hnorm : NormalizedWeights w) (hend : EndpointAssumption w) :
    Tendsto (fun α : ℝ => limsup (fun n => (exponentialRace (w n)).real
      {e | 0 < (fixedPoints (raceDraw e)).count {x | α < x.val}}) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```


## Luce/Section4CountLaw.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountLaw.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Luce
variable {X : Type*} [MeasurableSpace X]
section Topology
variable [TopologicalSpace X] [OpensMeasurableSpace X]
```

### finitePoissonLaw_count_univ

theorem; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountLaw.lean:22)

Section 4: the total count of a finite Poisson random measure has the
scalar Poisson law with parameter equal to the full intensity mass.

```lean
theorem finitePoissonLaw_count_univ (ν : FiniteMeasure X) :
    (finitePoissonLaw ν).map (fun ξ => ξ.count Set.univ) = poissonMeasure ν.mass
```

### FinitePointMeasure.continuous_count_univ

theorem; [source line 39](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountLaw.lean:39)

Section 4: evaluation on the whole spatial space is continuous even
as a natural-valued observable, because finite point measures have integer mass.

```lean
theorem FinitePointMeasure.continuous_count_univ :
    Continuous (fun ξ : FinitePointMeasure X => ξ.count Set.univ)
```

### pointCountSingletonTest

def; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountLaw.lean:52)

A bounded continuous test for any specified value of the total count.

```lean
def pointCountSingletonTest (k : ℕ) : FinitePointMeasure X →ᵇ ℝ where
  toFun ξ := if ξ.count Set.univ = k then 1 else 0
  continuous_toFun :=
    (show Continuous (fun n : ℕ => if n = k then (1 : ℝ) else 0) from
      continuous_of_discreteTopology).comp FinitePointMeasure.continuous_count_univ
  map_bounded' := ⟨1, fun ξ ζ => by
    rw [Real.dist_eq]
    split_ifs <;> norm_num⟩
```

### integral_pointCountSingletonTest

theorem; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountLaw.lean:61)

```lean
theorem integral_pointCountSingletonTest (Q : Measure (FinitePointMeasure X)) (k : ℕ) :
    (∫ ξ, pointCountSingletonTest k ξ ∂Q) =
      (Q.map (fun ξ => ξ.count Set.univ)).real {k}
```

### integral_pointCountSingletonTest_finitePoissonLaw

theorem; [source line 77](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountLaw.lean:77)

```lean
theorem integral_pointCountSingletonTest_finitePoissonLaw (ν : FiniteMeasure X) (k : ℕ) :
    (∫ ξ, pointCountSingletonTest k ξ ∂finitePoissonLaw ν) =
      (poissonMeasure ν.mass).real {k}
```

### integral_pointCountSingletonTest_comp

theorem; [source line 83](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountLaw.lean:83)

The singleton test evaluates the count law on any underlying sample space.

```lean
theorem integral_pointCountSingletonTest_comp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → FinitePointMeasure X) (hZ : Measurable Z) (k : ℕ) :
    (∫ ω, pointCountSingletonTest k (Z ω) ∂P) =
      (P.map (fun ω => (Z ω).count Set.univ)).real {k}
```

### pointMeasure_count_singleton_tendsto

theorem; [source line 101](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountLaw.lean:101)

Section 4: weak convergence of point-measure laws gives pointwise
convergence of the actual total-count probability mass functions.

```lean
theorem pointMeasure_count_singleton_tendsto
    (μ : ℕ → Measure (FinitePointMeasure X)) (Q : Measure (FinitePointMeasure X))
    (hWeak : ∀ F : FinitePointMeasure X →ᵇ ℝ,
      Tendsto (fun n => ∫ ξ, F ξ ∂μ n) atTop (𝓝 (∫ ξ, F ξ ∂Q))) (k : ℕ) :
    Tendsto (fun n => ((μ n).map (fun ξ => ξ.count Set.univ)).real {k}) atTop
      (𝓝 ((Q.map (fun ξ => ξ.count Set.univ)).real {k}))
```

### pointMeasure_random_count_singleton_poisson_tendsto

theorem; [source line 112](D:/princeton/Research/Lean/Lean_luce/Luce/Section4CountLaw.lean:112)

Section 4: the total-count probability masses of random finite point
measures converge to scalar Poisson probability masses whenever their spatial
laws converge to the canonical finite Poisson law.

```lean
theorem pointMeasure_random_count_singleton_poisson_tendsto
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (Z : ∀ n, Ω n → FinitePointMeasure X)
    (hZ : ∀ n, Measurable (Z n)) (ν : FiniteMeasure X)
    (hWeak : ∀ F : FinitePointMeasure X →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (Z n ω) ∂P n) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw ν))) (k : ℕ) :
    Tendsto (fun n => ((P n).map (fun ω => (Z n ω).count Set.univ)).real {k}) atTop
      (𝓝 ((poissonMeasure ν.mass).real {k}))
```


## Luce/Section4Endpoint.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Endpoint.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### integral_sum_clockSurvivalIndicator

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Endpoint.lean:17)

Equation `eq:mean-survivors`, including its expectation interpretation.

```lean
theorem integral_sum_clockSurvivalIndicator {n : ℕ} (w : Weights n)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ e, ∑ i, clockSurvivalIndicator t i e ∂exponentialRace w) =
      meanSurvivors w.rate t
```

### tailFixedPointCount_expectation_eq

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Endpoint.lean:30)

Exact law transfer for the spatial tail expectation, without extra
measurability, integrability or no-ties assumptions on the clocks.

```lean
theorem tailFixedPointCount_expectation_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (w : Weights n) (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (E i) (expMeasure (w.rate i)) P)
    (hIndependent : iIndepFun E P) (α : ℝ) :
    (∫ ω, (tailFixedPointCount (fun i => E i ω) α : ℝ) ∂P) =
      ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace w
```

### section4_endpoint_bound

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Endpoint.lean:43)

Equation `eq:tail-explicit` with the literal `B = sqrt(n M)`.
The row size is written `n+1` to avoid an artificial nonempty-row hypothesis.
The condition `M ≤ n+1` expresses that these are terminal labels.

```lean
theorem section4_endpoint_bound {n M : ℕ} (w : Weights (n + 1))
    (hnorm : ∑ i, w.rate i = ((n + 1 : ℕ) : ℝ))
    (hM : 1 ≤ M) (hMn : M ≤ n + 1) {γ s : ℝ} (hγ : 0 < γ)
    (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (terminalCandidate n m))
    (hcut : meanSurvivors w.rate s = Real.sqrt ((n + 1 : ℕ) * (M : ℝ)))
    (hBM : (M : ℝ) ≤ (Real.sqrt ((n + 1 : ℕ) * (M : ℝ)) - 1) / 2)
    (hs : 1 / γ ≤ s) :
    (∫ e, (terminalFixedPointCount (terminalCandidate n) M e : ℝ) ∂exponentialRace w) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) *
        Real.sqrt ((n + 1 : ℕ) * (M : ℝ))) + 2 * Real.exp (-γ * s) ∧
    (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) *
        Real.sqrt ((n + 1 : ℕ) * (M : ℝ))) + 2 * Real.exp (-γ * s) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) *
        Real.sqrt ((n + 1 : ℕ) * (M : ℝ))) +
      2 * (2 * Real.sqrt ((n + 1 : ℕ) * (M : ℝ)) / (n + 1)) ^ (γ / 2)
```

### section4_tail_expectation_bound

theorem; [source line 74](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Endpoint.lean:74)

Equation `eq:tail-epsilon` for the exact spatial tail on arbitrary row
spaces. The same exponent and constant as the manuscript are retained.

```lean
theorem section4_tail_expectation_bound
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (hnorm : NormalizedWeights w) (hend : EndpointAssumption w)
    (E : (n : ℕ) → Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        limsup (fun n => ∫ ω,
          (tailFixedPointCount (fun i => E n i ω) (1 - ε) : ℝ) ∂P n) atTop ≤
          (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4)
```


## Luce/Section4EndpointWitness.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointWitness.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### endpoint_window_le_row_of_size_condition

lemma; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointWitness.lean:18)

The size side condition in `prop:endpoint-bound` already forces the
terminal window to fit inside the row. Thus the indexing premise of
`section4_endpoint_bound` imposes no additional mathematical restriction.

```lean
lemma endpoint_window_le_row_of_size_condition {N M : ℕ} (hM : 1 ≤ M)
    (hBM : (M : ℝ) ≤ (Real.sqrt ((N : ℝ) * M) - 1) / 2) : M ≤ N
```

### eventually_terminal_rates_of_endpoint_witness

lemma; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointWitness.lean:31)

The source's closed terminal-neighborhood condition supplies the exact
rounded terminal labels, retaining its original γ. Shrinking ε₀ is harmless.

```lean
lemma eventually_terminal_rates_of_endpoint_witness
    (w : WeightArray) {γ ε₀ : ℝ} {n₀ : ℕ}
    (hε₀ : 0 < ε₀)
    (hrate : ∀ n : ℕ, n₀ ≤ n → ∀ k : Fin n,
      (1 - ε₀) * (n : ℝ) ≤ (k.val : ℝ) + 1 → γ ≤ (w n).rate k) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ m ∈ Finset.Icc 1 ⌈ε₁ * (n + 1)⌉₊,
        γ ≤ (w (n + 1)).rate (terminalCandidate n m)
```

### section4_tail_expectation_bound_of_endpoint_witness

theorem; [source line 63](D:/princeton/Research/Lean/Lean_luce/Luce/Section4EndpointWitness.lean:63)

Equation `eq:tail-epsilon`, retaining any specified admissible γ in the
constant and exponent. The clocks may live on arbitrary row probability spaces.

```lean
theorem section4_tail_expectation_bound_of_endpoint_witness
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (hnorm : NormalizedWeights w)
    (γ ε₀ : ℝ) (n₀ : ℕ) (hγ : 0 < γ) (hε₀ : 0 < ε₀)
    (hrate : ∀ n : ℕ, n₀ ≤ n → ∀ k : Fin n,
      (1 - ε₀) * (n : ℝ) ≤ (k.val : ℝ) + 1 → γ ≤ (w n).rate k)
    (E : (n : ℕ) → Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      limsup (fun n => ∫ ω,
        (tailFixedPointCount (fun i => E n i ω) (1 - ε) : ℝ) ∂P n) atTop ≤
        (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4)
```


## Luce/Section4Fatou.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Fatou.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped Topology
namespace Luce
```

### ConvergesInProbability.le_limsup_integral

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Fatou.lean:21)

Nonnegative variables converging in probability to a constant have
expectation limsup at least that constant. Eventual boundedness is explicit
because a real-valued limsup is totalized for unbounded sequences. In the
Section 4 application it is supplied by the proved endpoint estimate.

```lean
theorem ConvergesInProbability.le_limsup_integral
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : ∀ n, Ω n → ℝ} {c : ℝ}
    (hX : ConvergesInProbability P X c)
    (hmeas : ∀ n, Measurable (X n)) (hint : ∀ n, Integrable (X n) (P n))
    (hpos : ∀ n ω, 0 ≤ X n ω) (hc : 0 ≤ c)
    (hbounded : IsBoundedUnder (· ≤ ·) atTop (fun n => ∫ ω, X n ω ∂P n)) :
    c ≤ limsup (fun n => ∫ ω, X n ω ∂P n) atTop
```


## Luce/Section4FullIntensity.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4FullIntensity.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace Luce
```

### fullIntensity

def; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section4FullIntensity.lean:18)

The manuscript's full diagonal intensity as a finite measure on [0,1].

```lean
def fullIntensity (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    FiniteMeasure (Icc (0 : ℝ) 1) :=
  FiniteMeasure.map
    (⟨interiorDensityMeasure f 1, section4_full_intensity_finite w f hnorm hf hend⟩ :
      FiniteMeasure ℝ) (projIcc 0 1 zero_le_one)
```

### fullIntensity_projection_recovery

theorem; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section4FullIntensity.lean:26)

Projection recovers exactly the real-line density, including its support.

```lean
theorem fullIntensity_projection_recovery
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    (fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1)).map Subtype.val =
      interiorDensityMeasure f 1
```

### integral_fullIntensity

theorem; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section4FullIntensity.lean:44)

Integration against the full intensity is integration of the literal
diagonal density in `eq:intensity-tail-bound`. Endpoints have Lebesgue mass zero.

```lean
theorem integral_fullIntensity
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    (∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1))) =
      ∫ x in Ioo (0 : ℝ) 1, g (projIcc 0 1 zero_le_one x) * profileDiagonal f x
```

### fullIntensity_mass

theorem; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section4FullIntensity.lean:64)

The Poisson parameter is exactly the real integral defining λ in the paper.

```lean
theorem fullIntensity_mass
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    ((fullIntensity w f hnorm hf hend).mass : ℝ) =
      ∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x
```

### tendsto_integral_interiorIntensity_full_of_tendsto

theorem; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section4FullIntensity.lean:76)

Interior continuous-test integrals converge to the full integral, the
intensity-side limiting step in `fixed_points.tex:950–955`.

```lean
theorem tendsto_integral_interiorIntensity_full_of_tendsto
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {α : ι → ℝ}
    (hα : ∀ i, α i < 1) (hlim : Tendsto α l (𝓝 1))
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    Tendsto (fun i => ∫ y, g y
      ∂(interiorIntensity w f hf (α i) (hα i) : Measure (Icc (0 : ℝ) 1))) l
      (𝓝 (∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1))))
```

### tendsto_integral_interiorIntensity_full

theorem; [source line 120](D:/princeton/Research/Lean/Lean_luce/Luce/Section4FullIntensity.lean:120)

Real-parameter version for the left limit α ↑ 1.

```lean
theorem tendsto_integral_interiorIntensity_full
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    Tendsto (fun α : ℝ => if hα : α < 1 then
      ∫ y, g y ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1))
      else ∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1)))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1))))
```

### tendsto_laplace_finitePoissonLaw_interior_full

theorem; [source line 148](D:/princeton/Research/Lean/Lean_luce/Luce/Section4FullIntensity.lean:148)

The finite Poisson Laplace functionals converge as the cutoff is removed;
this is the limiting-law half of `fixed_points.tex:950–955`.

```lean
theorem tendsto_laplace_finitePoissonLaw_interior_full
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
    Tendsto (fun α : ℝ => if hα : α < 1 then
      ∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (interiorIntensity w f hf α hα)
      else ∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (fullIntensity w f hnorm hf hend))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))
```


## Luce/Section4Intensity.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce
```

### interiorDensityMeasure_restrict

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:17)

Compatibility of the literal interior densities under restriction.

```lean
theorem interiorDensityMeasure_restrict (f : ℝ → ℝ) (α β : ℝ) :
    (interiorDensityMeasure f α).restrict (Iic β) =
      interiorDensityMeasure f (min α β)
```

### terminalIntensityTest

def; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:28)

A continuous terminal cutoff, identically one at and beyond b.

```lean
def terminalIntensityTest (a b : ℝ) : Icc (0 : ℝ) 1 →ᵇ ℝ where
  toFun x := max 0 (min 1 ((x.val - a) / (b - a)))
  continuous_toFun := continuous_const.max (continuous_const.min
    ((continuous_subtype_val.sub continuous_const).div_const _))
  map_bounded' := ⟨1, fun x y => by
    rw [Real.dist_eq, abs_le]
    have hx0 : 0 ≤ max 0 (min 1 ((x.val - a) / (b - a))) := le_max_left _ _
    have hy0 : 0 ≤ max 0 (min 1 ((y.val - a) / (b - a))) := le_max_left _ _
    have hx1 : max 0 (min 1 ((x.val - a) / (b - a))) ≤ (1 : ℝ) :=
      max_le (by norm_num) (min_le_left _ _)
    have hy1 : max 0 (min 1 ((y.val - a) / (b - a))) ≤ (1 : ℝ) :=
      max_le (by norm_num) (min_le_left _ _)
    constructor <;> linarith⟩
```

### terminalIntensityTest_bounds

lemma; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:42)

```lean
lemma terminalIntensityTest_bounds (a b : ℝ) (x : Icc (0 : ℝ) 1) :
    0 ≤ terminalIntensityTest a b x ∧ terminalIntensityTest a b x ≤ 1
```

### terminalIntensityTest_zero

lemma; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:46)

```lean
lemma terminalIntensityTest_zero {a b : ℝ} (hab : a < b)
    (x : Icc (0 : ℝ) 1) (hx : x.val ≤ a) : terminalIntensityTest a b x = 0
```

### terminalIntensityTest_one

lemma; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:52)

```lean
lemma terminalIntensityTest_one {a b : ℝ} (hab : a < b)
    (x : Icc (0 : ℝ) 1) (hx : b ≤ x.val) : terminalIntensityTest a b x = 1
```

### interiorDensityMeasure_tail_le_test

theorem; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:62)

An upper bound on the continuous terminal test bounds the mass strictly
beyond its upper cutoff. This uses only the already finite interior measure.

```lean
theorem interiorDensityMeasure_tail_le_test
    (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f)
    {a b β : ℝ} (hab : a < b) (hβ : β < 1) :
    (interiorDensityMeasure f β).real (Ioi b) ≤
      ∫ y, terminalIntensityTest a b y
        ∂(interiorIntensity w f hf β hβ : Measure (Icc (0 : ℝ) 1))
```

### interiorDensityMeasure_mono

lemma; [source line 98](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:98)

```lean
lemma interiorDensityMeasure_mono (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    interiorDensityMeasure f a ≤ interiorDensityMeasure f b
```

### section4_interior_intensity_bounded

theorem; [source line 105](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:105)

The endpoint estimate prevents the total interior intensity from
diverging as its upper endpoint increases to one.

```lean
theorem section4_interior_intensity_bounded
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    ∃ C : ℝ, ∀ β : ℝ, β < 1 → (interiorDensityMeasure f β).real univ ≤ C
```

### fullDensityMeasure_restrict_Iio

lemma; [source line 144](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:144)

The singleton at one has no density mass, so the increasing open-end
exhaustion captures the entire full intensity.

```lean
lemma fullDensityMeasure_restrict_Iio (f : ℝ → ℝ) :
    (interiorDensityMeasure f 1).restrict (Iio 1) = interiorDensityMeasure f 1
```

### section4_full_intensity_finite

theorem; [source line 161](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:161)

Equation `eq:intensity-tail-bound`: the full, literal diagonal density
measure is finite under exactly the paper's assumptions. No finiteness or
uniform-integrability premise is carried through from the helper theorems.

```lean
theorem section4_full_intensity_finite
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    IsFiniteMeasure (interiorDensityMeasure f 1)
```

### aestronglyMeasurable_profileDiagonal_full

lemma; [source line 201](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:201)

The diagonal is measurably defined over the full open interval by its
already proved local integrability. No endpoint value is prescribed.

```lean
lemma aestronglyMeasurable_profileDiagonal_full
    {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f) :
    AEStronglyMeasurable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1))
```

### section4_profileDiagonal_integrable

theorem; [source line 221](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:221)

The full real Lebesgue integral in the definition of λ is a genuine
integral of an integrable function, rather than a totalized divergent integral.

```lean
theorem section4_profileDiagonal_integrable
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1))
```

### section4_intensity_tail_tendsto

theorem; [source line 238](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Intensity.lean:238)

The second assertion of `eq:intensity-tail-bound`, with Lebesgue endpoint
conventions made explicit. Integrability has already been proved above.

```lean
theorem section4_intensity_tail_tendsto
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    Tendsto (fun α : ℝ => ∫ x in Ioo α 1, profileDiagonal f x)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```


## Luce/Section4IntensityEstimate.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4IntensityEstimate.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology BoundedContinuousFunction
namespace Luce
```

### integrable_interior_observed_test

lemma; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section4IntensityEstimate.lean:16)

```lean
lemma integrable_interior_observed_test {n : ℕ} (w : Weights n) (β : ℝ)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    Integrable (fun e => ∫ y, g y ∂((interiorFixedPoints β (raceDraw e)).toFiniteMeasure :
      Measure (Icc (0 : ℝ) 1))) (exponentialRace w)
```

### interior_observed_test_le_tail

lemma; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section4IntensityEstimate.lean:32)

A continuous test in [0,1], zero before α, counts no more than the actual
terminal fixed points. This holds for every interior cutoff β.

```lean
lemma interior_observed_test_le_tail {n : ℕ} (e : Fin n → ℝ)
    (hinj : Function.Injective e) (α β : ℝ) (g : Icc (0 : ℝ) 1 →ᵇ ℝ)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hsupport : ∀ x, x.val ≤ α → g x = 0) :
    (∫ y, g y ∂((interiorFixedPoints β (raceDraw e)).toFiniteMeasure :
      Measure (Icc (0 : ℝ) 1))) ≤ (tailFixedPointCount e α : ℝ)
```

### integral_interior_observed_test_le_tail

lemma; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section4IntensityEstimate.lean:60)

```lean
lemma integral_interior_observed_test_le_tail {n : ℕ} (w : Weights n)
    (α β : ℝ) (g : Icc (0 : ℝ) 1 →ᵇ ℝ)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hsupport : ∀ x, x.val ≤ α → g x = 0) :
    (∫ e, ∫ y, g y ∂((interiorFixedPoints β (raceDraw e)).toFiniteMeasure :
      Measure (Icc (0 : ℝ) 1)) ∂exponentialRace w) ≤
      ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace w
```

### section4_intensity_test_bound

theorem; [source line 75](D:/princeton/Research/Lean/Lean_luce/Luce/Section4IntensityEstimate.lean:75)

The central endpoint intensity estimate for every nonnegative continuous
test bounded by one and supported in the tail. All bounds and convergence
hypotheses have been discharged from the paper's normalization, profile and
endpoint assumptions. The estimate is uniform in the interior cutoff β.

```lean
theorem section4_intensity_test_bound
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ → ∀ β : ℝ, ∀ hβ : β < 1,
      ∀ g : Icc (0 : ℝ) 1 →ᵇ ℝ,
        (∀ x, 0 ≤ g x ∧ g x ≤ 1) → (∀ x, x.val ≤ 1 - ε → g x = 0) →
        (∫ y, g y ∂(interiorIntensity w f hf β hβ : Measure (Icc (0 : ℝ) 1))) ≤
          (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4)
```


## Luce/Section4Poisson.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Poisson.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal
namespace Luce
```

### section4_full_laplace

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Poisson.lean:20)

The full process has the Poisson Laplace limit, under exactly the
normalized model and the paper's profile and endpoint assumptions.

```lean
theorem section4_full_laplace
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
    Tendsto (fun n => ∫ e, pointLaplace (fun x => (g x : ℝ))
      (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))
```

### section4_full_poisson

theorem; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Poisson.lean:61)

Equation `eq:point-process-limit`: convergence of the actual full
finite point measure in its weak topology. Every bounded continuous test
of the point measure is allowed, and all approximation and tightness
conditions have been proved from the model assumptions.

```lean
theorem section4_full_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))
```

### section4_full_poisson_general

theorem; [source line 97](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Poisson.lean:97)

The full point-process limit for every Luce permutation realization.
The row masses are precisely `eq:luce-law`; no coupling between rows or
asymptotic hypothesis beyond the manuscript assumptions is required.

```lean
theorem section4_full_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ)
    (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))
```


## Luce/Section4ShellFullIntensity.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellFullIntensity.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace Luce.Shell
```

### fullIntensity

def; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellFullIntensity.lean:18)

The manuscript's full diagonal intensity as a finite measure on [0,1].

```lean
def fullIntensity (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    FiniteMeasure (Icc (0 : ℝ) 1) :=
  FiniteMeasure.map
    (⟨interiorDensityMeasure f 1, section4_full_intensity_finite w f hnorm hf hend⟩ :
      FiniteMeasure ℝ) (projIcc 0 1 zero_le_one)
```

### fullIntensity_projection_recovery

theorem; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellFullIntensity.lean:26)

Projection recovers exactly the real-line density, including its support.

```lean
theorem fullIntensity_projection_recovery
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    (fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1)).map Subtype.val =
      interiorDensityMeasure f 1
```

### integral_fullIntensity

theorem; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellFullIntensity.lean:44)

Integration against the full intensity is integration of the literal
diagonal density in `eq:intensity-tail-bound`. Endpoints have Lebesgue mass zero.

```lean
theorem integral_fullIntensity
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    (∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1))) =
      ∫ x in Ioo (0 : ℝ) 1, g (projIcc 0 1 zero_le_one x) * profileDiagonal f x
```

### fullIntensity_mass

theorem; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellFullIntensity.lean:64)

The Poisson parameter is exactly the real integral defining λ in the paper.

```lean
theorem fullIntensity_mass
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    ((fullIntensity w f hnorm hf hend).mass : ℝ) =
      ∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x
```

### tendsto_integral_interiorIntensity_full_of_tendsto

theorem; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellFullIntensity.lean:76)

Interior continuous-test integrals converge to the full integral, the
intensity-side limiting step in `fixed_points.tex:950–955`.

```lean
theorem tendsto_integral_interiorIntensity_full_of_tendsto
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {α : ι → ℝ}
    (hα : ∀ i, α i < 1) (hlim : Tendsto α l (𝓝 1))
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    Tendsto (fun i => ∫ y, g y
      ∂(interiorIntensity w f hf (α i) (hα i) : Measure (Icc (0 : ℝ) 1))) l
      (𝓝 (∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1))))
```

### tendsto_integral_interiorIntensity_full

theorem; [source line 120](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellFullIntensity.lean:120)

Real-parameter version for the left limit α ↑ 1.

```lean
theorem tendsto_integral_interiorIntensity_full
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    Tendsto (fun α : ℝ => if hα : α < 1 then
      ∫ y, g y ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1))
      else ∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1)))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1))))
```

### tendsto_laplace_finitePoissonLaw_interior_full

theorem; [source line 148](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellFullIntensity.lean:148)

The finite Poisson Laplace functionals converge as the cutoff is removed;
this is the limiting-law half of `fixed_points.tex:950–955`.

```lean
theorem tendsto_laplace_finitePoissonLaw_interior_full
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
    Tendsto (fun α : ℝ => if hα : α < 1 then
      ∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (interiorIntensity w f hf α hα)
      else ∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (fullIntensity w f hnorm hf hend))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))
```


## Luce/Section4ShellIntensity.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellIntensity.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.Shell
```

### section4_full_intensity_finite

theorem; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellIntensity.lean:8)

```lean
theorem section4_full_intensity_finite
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    IsFiniteMeasure (interiorDensityMeasure f 1)
```

### aestronglyMeasurable_profileDiagonal_full

lemma; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellIntensity.lean:48)

The diagonal is measurably defined over the full open interval by its
already proved local integrability. No endpoint value is prescribed.

```lean
lemma aestronglyMeasurable_profileDiagonal_full
    {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f) :
    AEStronglyMeasurable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1))
```

### section4_profileDiagonal_integrable

theorem; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellIntensity.lean:68)

The full real Lebesgue integral in the definition of λ is a genuine
integral of an integrable function, rather than a totalized divergent integral.

```lean
theorem section4_profileDiagonal_integrable
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1))
```

### section4_intensity_tail_tendsto

theorem; [source line 85](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellIntensity.lean:85)

The second assertion of `eq:intensity-tail-bound`, with Lebesgue endpoint
conventions made explicit. Integrability has already been proved above.

```lean
theorem section4_intensity_tail_tendsto
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    Tendsto (fun α : ℝ => ∫ x in Ioo α 1, profileDiagonal f x)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```


## Luce/Section4ShellIntensityBound.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellIntensityBound.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.Shell
```

### intensity_test_bound

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellIntensityBound.lean:9)

```lean
theorem intensity_test_bound (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    ∀ η : ℝ, 0 < η → ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      ∀ β : ℝ, ∀ hβ : β < 1, ∀ g : Icc (0 : ℝ) 1 →ᵇ ℝ,
        (∀ x, 0 ≤ g x ∧ g x ≤ 1) → (∀ x, x.val ≤ a → g x = 0) →
        (∫ y, g y ∂(interiorIntensity w f hf β hβ : Measure (Icc (0 : ℝ) 1))) ≤ η
```

### section4_interior_intensity_bounded

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellIntensityBound.lean:30)

```lean
theorem section4_interior_intensity_bounded
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    ∃ C : ℝ, ∀ β : ℝ, β < 1 → (interiorDensityMeasure f β).real univ ≤ C
```


## Luce/Section4ShellPoisson.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellPoisson.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal
namespace Luce.Shell
```

### section4_full_laplace

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellPoisson.lean:20)

The full process has the Poisson Laplace limit, under exactly the
normalized model and the paper's profile and endpoint assumptions.

```lean
theorem section4_full_laplace
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
    Tendsto (fun n => ∫ e, pointLaplace (fun x => (g x : ℝ))
      (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))
```

### section4_full_poisson

theorem; [source line 57](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellPoisson.lean:57)

Equation `eq:point-process-limit`: convergence of the actual full
finite point measure in its weak topology. Every bounded continuous test
of the point measure is allowed, and all approximation and tightness
conditions have been proved from the model assumptions.

```lean
theorem section4_full_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))
```

### section4_full_poisson_general

theorem; [source line 93](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellPoisson.lean:93)

The full point-process limit for every Luce permutation realization.
The row masses are precisely `eq:luce-law`; no coupling between rows or
asymptotic hypothesis beyond the manuscript assumptions is required.

```lean
theorem section4_full_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ)
    (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))
```


## Luce/Section4ShellTheorem.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellTheorem.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.Shell
```

### section4_main_poisson

theorem; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellTheorem.lean:8)

```lean
theorem section4_main_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))) ∧
    Tendsto (fun n => probabilityTotalVariation (raceFixedPointCountLaw (w n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0)
```

### section4_main_poisson_general

theorem; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellTheorem.lean:26)

The same complete theorem for arbitrary row probability spaces and
measurable Luce permutations with the manuscript's exact finite masses.
Cross-row independence, regularity of the profile beyond L¹ convergence,
and global upper/lower rate bounds are not hypotheses.

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


## Luce/Section4ShellTotalVariation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellTotalVariation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.Shell
```

### fullIntensity_mass_eq_toNNReal_integral

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellTotalVariation.lean:9)

```lean
theorem fullIntensity_mass_eq_toNNReal_integral
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    (fullIntensity w f hnorm hf hend).mass =
      Real.toNNReal (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)
```

### section4_count_poisson

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellTotalVariation.lean:19)

Equation `eq:count-poisson`: the full count law converges in probability
total variation to Poisson with the literal diagonal integral as parameter.

```lean
theorem section4_count_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
    Tendsto (fun n => probabilityTotalVariation (raceFixedPointCountLaw (w n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0)
```

### section4_count_poisson_general

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellTotalVariation.lean:33)

The total-variation conclusion for arbitrary realizations of the Luce
law, with only its defining finite masses and the manuscript assumptions.

```lean
theorem section4_count_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    Tendsto (fun n => probabilityTotalVariation
      (fixedPointCountLaw (P n) (π n) (hπ n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0)
```


## Luce/Section4Theorem.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Theorem.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace Luce
```

### fixedPoints_realMeasure

theorem; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Theorem.lean:18)

The full process, mapped to the real line, is literally `eq:fixed-process`.

```lean
theorem fixedPoints_realMeasure {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ((fixedPoints π).toFiniteMeasure : Measure (Icc (0 : ℝ) 1)).map Subtype.val =
      ∑ k : Fin n, if π.symm k = k then
        Measure.dirac (((k.val : ℝ) + 1) / n) else 0
```

### section4_lambda_nonneg

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Theorem.lean:30)

The real parameter used by the scalar Poisson law is nonnegative.

```lean
theorem section4_lambda_nonneg
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    0 ≤ ∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x
```

### section4_main_poisson

theorem; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Theorem.lean:41)

The full conclusion of Theorem `thm:main-poisson`, in the canonical
independent exponential-clock model. No missing estimate or convergence
statement is assumed. Every bounded weak-continuous point-measure test is
quantified, and the count conclusion uses the exact probability-TV convention.

```lean
theorem section4_main_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))) ∧
    Tendsto (fun n => probabilityTotalVariation (raceFixedPointCountLaw (w n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0)
```

### section4_main_poisson_general

theorem; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section4Theorem.lean:59)

The same complete theorem for arbitrary row probability spaces and
measurable Luce permutations with the manuscript's exact finite masses.
Cross-row independence, regularity of the profile beyond L¹ convergence,
and global upper/lower rate bounds are not hypotheses.

```lean
theorem section4_main_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
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


## Luce/Section4TotalVariation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal
namespace Luce
```

### fixedPointCount

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean:21)

The manuscript's random variable `X_n`, extracted from its literal point measure.

```lean
def fixedPointCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (fixedPoints π).count univ
```

### fixedPointCount_eq_card

theorem; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean:26)

The total-mass representation counts exactly the fixed labels, with no
inverse-permutation or endpoint discrepancy. The statement also covers `n = 0`.

```lean
theorem fixedPointCount_eq_card {n : ℕ} (π : Equiv.Perm (Fin n)) :
    fixedPointCount π = (Finset.univ.filter fun k => π k = k).card
```

### measurable_fixedPoints

theorem; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean:38)

Fixed-point measures are measurable on the finite discrete permutation space.

```lean
theorem measurable_fixedPoints (n : ℕ) :
    @Measurable (Equiv.Perm (Fin n)) (FinitePointMeasure (Icc (0 : ℝ) 1)) ⊤
      inferInstance fixedPoints
```

### fixedPointCountLaw

def; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean:43)

The actual total-count distribution on an arbitrary row probability space.

```lean
def fixedPointCountLaw {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π) : ProbabilityMeasure ℕ :=
  ⟨P.map (fun ω => fixedPointCount (π ω)), P.isProbabilityMeasure_map
    ((FinitePointMeasure.measurable_count MeasurableSet.univ).comp
      ((measurable_fixedPoints n).comp hπ)).aemeasurable⟩
```

### raceFixedPointCountLaw

def; [source line 51](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean:51)

The canonical exponential-race realization of the fixed-point count law.

```lean
def raceFixedPointCountLaw {n : ℕ} (w : Weights n) : ProbabilityMeasure ℕ :=
  fixedPointCountLaw (exponentialRace w) raceDraw (measurable_raceDraw n)
```

### poissonProbabilityMeasure

def; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean:55)

The standard scalar Poisson law, with its proved probability normalization.

```lean
def poissonProbabilityMeasure (r : ℝ≥0) : ProbabilityMeasure ℕ :=
  ⟨poissonMeasure r, inferInstance⟩
```

### fixedPointCountLaw_totalVariation_of_pointProcess

theorem; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean:61)

The generic final passage of Section 4: the proved spatial limit gives
pointwise count probabilities, then the discrete Scheffé theorem gives TV.
The manuscript-specific theorems below discharge the spatial premise.

```lean
theorem fixedPointCountLaw_totalVariation_of_pointProcess
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (ν : FiniteMeasure (Icc (0 : ℝ) 1))
    (hWeak : ∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw ν))) :
    Tendsto (fun n => probabilityTotalVariation
      (fixedPointCountLaw (P n) (π n) (hπ n)) (poissonProbabilityMeasure ν.mass))
      atTop (𝓝 0)
```

### fullIntensity_mass_eq_toNNReal_integral

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean:81)

The scalar Poisson parameter is exactly the manuscript's Lebesgue
integral. Taking its nonnegative subtype does not truncate any negative value.

```lean
theorem fullIntensity_mass_eq_toNNReal_integral
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    (fullIntensity w f hnorm hf hend).mass =
      Real.toNNReal (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)
```

### section4_count_poisson

theorem; [source line 91](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean:91)

Equation `eq:count-poisson`: the full count law converges in probability
total variation to Poisson with the literal diagonal integral as parameter.

```lean
theorem section4_count_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    Tendsto (fun n => probabilityTotalVariation (raceFixedPointCountLaw (w n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0)
```

### section4_count_poisson_general

theorem; [source line 105](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TotalVariation.lean:105)

The total-variation conclusion for arbitrary realizations of the Luce
law, with only its defining finite masses and the manuscript assumptions.

```lean
theorem section4_count_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    Tendsto (fun n => probabilityTotalVariation
      (fixedPointCountLaw (P n) (π n) (hπ n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0)
```


## Luce/Section5.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5.lean)

No declarations; imports or audit commands only.


## Luce/Section5BlockIntegral.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BlockIntegral.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce
```

### bulkCycleTraceIntensity

def; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BlockIntegral.lean:10)

The manuscript's truncated intensity, on the literal closed cube.

```lean
def bulkCycleTraceIntensity (f : ℝ → ℝ) (α : ℝ) (k : ℕ) : ℝ :=
  (∫ x in cyclicBulkCube (k+1) α, cycleTraceIntegrand f k x) / (k+1 : ℝ)
```

### block_density_integral_factorization

theorem; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BlockIntegral.lean:13)

```lean
theorem block_density_integral_factorization (f : ℝ → ℝ) (L : ℕ)
    (m : Fin L → ℕ) (μ : Measure ℝ) [SigmaFinite μ] :
    (∫ x, ∏ a : Section5.CycleVertex L m,
      cyclicProfileDensity f (x a) (x (Section5.cycleBlockPermutation L m a))
      ∂Measure.pi (fun _ => μ)) =
      ∏ ell : Fin L, (∫ x, cycleTraceIntegrand f ell.val x
        ∂Measure.pi (fun _ : Fin (ell.val+1) => μ)) ^ m ell
```

### cyclic_integral_reindex

theorem; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BlockIntegral.lean:36)

Reindexing by a finite equivalence preserves the literal cyclic integral.

```lean
theorem cyclic_integral_reindex {V : Type*} [Fintype V] {r : ℕ}
    (e : V ≃ Fin r) (τ : Equiv.Perm V) (f : ℝ → ℝ)
    (μ : Measure ℝ) [SigmaFinite μ] :
    (∫ x, ∏ a, cyclicProfileDensity f (x a) (x ((e.symm.trans (τ.trans e)) a))
      ∂Measure.pi (fun _ : Fin r => μ)) =
      ∫ x, ∏ a, cyclicProfileDensity f (x a) (x (τ a))
        ∂Measure.pi (fun _ : V => μ)
```

### canonical_block_integral_eq_intensity_product

theorem; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BlockIntegral.lean:55)

The full block integral with its original rotation divisor factors
into the individual manuscript intensities. This identity is unconditional
in the density; the separate local-limit proof supplies its analytic use.

```lean
theorem canonical_block_integral_eq_intensity_product (f : ℝ → ℝ)
    (L : ℕ) (m : Fin L → ℕ) (α : ℝ) :
    ((∫ x in cyclicBulkCube (Fintype.card (Section5.CycleVertex L m)) α,
      ∏ a, cyclicProfileDensity f (x a) (x (factorialBlockPermutation L m a))) /
        ∏ ell : Fin L, ((ell.val+1 : ℕ) : ℝ)^m ell) =
      ∏ ell : Fin L, bulkCycleTraceIntensity f α ell.val ^ m ell
```


## Luce/Section5BlockProductMeasure.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BlockProductMeasure.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce
```

### measurePreserving_block_uncurry

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BlockProductMeasure.lean:11)

Grouping finitely many independent coordinates into blocks preserves
their product measure. This is a representation theorem, not an independence
assumption on the Luce model.

```lean
theorem measurePreserving_block_uncurry {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (μ : (i : ι) → κ i → Measure ℝ)
    [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (_ : ι) (_ : κ _) => ℝ)).symm
      (Measure.pi (fun i => Measure.pi (μ i)))
      (Measure.pi (fun p : Sigma κ => μ p.1 p.2))
```

### integral_block_product

theorem; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BlockProductMeasure.lean:34)

Fubini for functions of disjoint original blocks, with no assumed
integrability or boundedness of the coordinate density.

```lean
theorem integral_block_product {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (μ : (i : ι) → κ i → Measure ℝ)
    [∀ i j, SigmaFinite (μ i j)] (F : (i : ι) → (κ i → ℝ) → ℝ) :
    (∫ x, ∏ i, F i (fun j => x ⟨i,j⟩)
      ∂Measure.pi (fun p : Sigma κ => μ p.1 p.2)) =
      ∏ i, ∫ x, F i x ∂Measure.pi (μ i)
```


## Luce/Section5BulkCylinder.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinder.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### sum_mass_event_next_le

lemma; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinder.lean:28)

Sum the exact next-draw law over histories satisfying a preceding event.
This is the conditional-draw version of the memorylessness step at 1020–1033.

```lean
lemma sum_mass_event_next_le {n : ℕ} (w : Weights n) (k i : Fin n)
    (A : Equiv.Perm (Fin n) → Prop) [DecidablePred A] {c : ℝ}
    (hA : ∀ σ τ, prefixAgrees σ τ k.val → (A σ ↔ A τ))
    (hc : ∀ σ, w.choice (remaining σ k) i ≤ c) :
    (∑ τ : Equiv.Perm (Fin n), if A τ ∧ τ k = i then w.mass τ else 0) ≤
      c * ∑ τ : Equiv.Perm (Fin n), if A τ then w.mass τ else 0
```

### sum_mass_cylinder_le

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinder.lean:81)

Iterate the one-step law at the prescribed ranks in increasing order.
The finite set records distinct ranks; repeated labels are allowed here
(their inconsistent assignment event has zero probability).

```lean
theorem sum_mass_cylinder_le {n : ℕ} (w : Weights n) (s : Finset (Fin n))
    (label : Fin n → Fin n) {B : ℝ} (hB : 0 < B)
    (hrem : ∀ k ∈ s, ∀ σ : Equiv.Perm (Fin n), B ≤ w.total (remaining σ k)) :
    (∑ σ : Equiv.Perm (Fin n),
      if ∀ k ∈ s, σ k = label k then w.mass σ else 0) ≤
        ∏ k ∈ s, w.rate (label k) / B
```

### card_removed_before_rank

lemma; [source line 125](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinder.lean:125)

The removed labels before zero-based rank `k` have cardinality `k`.
This records the permutation multiplicity used in applying the reservoir.

```lean
lemma card_removed_before_rank {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    (Finset.univ \ remaining σ k).card = k.val
```

### ProfileLimit.eventually_bulk_remaining_rate

theorem; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinder.lean:141)

The reservoir controls every actual draw-history denominator up to `α n`.
Neither the history nor the set of marked labels is fixed in advance.

```lean
theorem ProfileLimit.eventually_bulk_remaining_rate {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin n, (k.val : ℝ) + 1 ≤ α * n →
        ∀ σ : Equiv.Perm (Fin n), b * n ≤ (w n).total (remaining σ k)
```

### sum_mass_marked_cylinder_le

theorem; [source line 160](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinder.lean:160)

Distinct ranks are encoded by an embedding, and their products are
transported without an extra factorial. The labels need not be distinct for
this stronger auxiliary estimate.

```lean
theorem sum_mass_marked_cylinder_le {n r : ℕ} (w : Weights n)
    (i : Fin r → Fin n) (j : Fin r ↪ Fin n) {B : ℝ} (hB : 0 < B)
    (hrem : ∀ a : Fin r, ∀ σ : Equiv.Perm (Fin n), B ≤ w.total (remaining σ (j a))) :
    (∑ σ : Equiv.Perm (Fin n), if ∀ a, σ (j a) = i a then w.mass σ else 0) ≤
      (∏ a : Fin r, w.rate (i a)) / B ^ r
```

### raceDraw_event_probability

lemma; [source line 178](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinder.lean:178)

Actual exponential-race events have the finite sums of the full Luce
masses, by the previously proved law of the sorted clocks.

```lean
lemma raceDraw_event_probability {n : ℕ} (w : Weights n)
    (A : Equiv.Perm (Fin n) → Prop) [DecidablePred A] :
    (exponentialRace w).real {clocks | A (raceDraw clocks)} =
      ∑ σ : Equiv.Perm (Fin n), if A σ then w.mass σ else 0
```

### ProfileLimit.weighted_bulk_draw_cylinder

theorem; [source line 204](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinder.lean:204)

Equation `eq:weighted-bulk-cylinder` in draw-order notation. The same
constant works for every choice of distinct labels and distinct bulk ranks.
The empty tuple is also included and gives the identity probability one.

```lean
theorem ProfileLimit.weighted_bulk_draw_cylinder {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a : Fin r, ((j a).val : ℝ) + 1 ≤ α * n) →
        (exponentialRace (w n)).real {clocks | ∀ a, raceDraw clocks (j a) = i a} ≤
          K / (n : ℝ) ^ r * ∏ a : Fin r, (w n).rate (i a)
```

### raceRank_eq_iff_raceDraw

lemma; [source line 226](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinder.lean:226)

Exact conversion from the paper's one-based rank convention to the
inverse draw permutation, on the full-probability event of distinct clocks.

```lean
lemma raceRank_eq_iff_raceDraw {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (i j : Fin n) :
    raceRank clocks i = j.val + 1 ↔ raceDraw clocks j = i
```

### ProfileLimit.weighted_bulk_cylinder

theorem; [source line 238](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinder.lean:238)

Equation `eq:weighted-bulk-cylinder` in the paper's exact rank convention.
All marked rates are unrestricted. Constants are uniform over distinct
marked labels and distinct prescribed ranks, and row zero is only omitted
by an eventual threshold. The case `r = 0` is proved as well.

```lean
theorem ProfileLimit.weighted_bulk_cylinder {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a : Fin r, ((j a).val : ℝ) + 1 ≤ α * n) →
        (exponentialRace (w n)).real
          {clocks | ∀ a, raceRank clocks (i a) = (j a).val + 1} ≤
          K / (n : ℝ) ^ r * ∏ a : Fin r, (w n).rate (i a)
```


## Luce/Section5BulkCylinderAll.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinderAll.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### earlyBulkCylinderConstant

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinderAll.lean:21)

A finite constant controlling every early-row source tuple. The extra
one handles the empty tuple and keeps the resulting bound positive.

```lean
def earlyBulkCylinderConstant (w : WeightArray) (r N : ℕ) : ℝ :=
  1 + ∑ m : Fin N, ∑ i : Fin r ↪ Fin m.val,
    (m.val : ℝ) ^ r / ∏ a, (w m.val).rate (i a)
```

### earlyBulkCylinderConstant_one_le

lemma; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinderAll.lean:25)

```lean
lemma earlyBulkCylinderConstant_one_le (w : WeightArray) (r N : ℕ) :
    1 ≤ earlyBulkCylinderConstant w r N
```

### earlyBulkCylinderConstant_ge

lemma; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinderAll.lean:38)

```lean
lemma earlyBulkCylinderConstant_ge (w : WeightArray) (r N n : ℕ) (hn : n < N)
    (i : Fin r ↪ Fin n) :
    (n : ℝ) ^ r / (∏ a, (w n).rate (i a)) ≤ earlyBulkCylinderConstant w r N
```

### ProfileLimit.weighted_bulk_cylinder_all

theorem; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkCylinderAll.lean:61)

The literal weighted bulk cylinder inequality for all n. Positive
weights make the finite initial-row constants finite; n=0 and r=0 are
handled explicitly, rather than concealed by totalized division.

```lean
theorem ProfileLimit.weighted_bulk_cylinder_all {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
          (exponentialRace (w n)).real
            {old | ∀ a, raceRank old (i a) = (j a).val + 1} ≤
            K / (n : ℝ) ^ r * ∏ a, (w n).rate (i a)
```


## Luce/Section5BulkPointMass.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkPointMass.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
```

### tendsto_of_finite_approximation

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkPointMass.lean:11)

A finite-approximation argument with the row limit taken before the
approximation order. Every premise is discharged for the cycle application
below by its polynomial limits and factorial remainder bounds.

```lean
theorem tendsto_of_finite_approximation
    (X : ℕ → ℝ) (A E : ℕ → ℕ → ℝ) (a b : ℕ → ℝ) (p : ℝ)
    (hA : ∀ K, Tendsto (A K) atTop (𝓝 (a K)))
    (hE : ∀ K, Tendsto (E K) atTop (𝓝 (b K)))
    (ha : Tendsto a atTop (𝓝 p)) (hb : Tendsto b atTop (𝓝 0))
    (herr : ∀ K n, |A K n-X n| ≤ E K n) : Tendsto X atTop (𝓝 p)
```

### bulk_cycle_point_indicator_limit

theorem; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkPointMass.lean:35)

Joint bulk point probabilities converge to the independent-Poisson
formula. Only the original normalization/profile assumptions are used.

```lean
theorem bulk_cycle_point_indicator_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z,
      (if (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q
        then (1 : ℝ) else 0) ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell, Real.exp (-bulkCycleTraceIntensity f α ell.val) *
        bulkCycleTraceIntensity f α ell.val ^ q ell / ((q ell).factorial : ℝ)))
```


## Luce/Section5BulkPointProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkPointProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators Topology
namespace Luce
```

### measurable_race_permutation_statistic

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkPointProbability.lean:9)

```lean
theorem measurable_race_permutation_statistic {n : ℕ} {E : Type*}
    [MeasurableSpace E] (F : Equiv.Perm (Fin n) → E) :
    Measurable (fun z : Fin n → ℝ => F (raceRankPermutation z))
```

### bulkCycleVectorPoissonLaw

def; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkPointProbability.lean:25)

```lean
def bulkCycleVectorPoissonLaw (f : ℝ → ℝ) (α : ℝ) (L : ℕ) : Measure (Fin L → ℕ) :=
  Measure.pi (fun ell => poissonMeasure (Real.toNNReal (bulkCycleTraceIntensity f α ell.val)))
```

### instance at line 28

instance; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkPointProbability.lean:28)

```lean
instance bulkCycleVectorPoissonLaw_probability (f : ℝ → ℝ) (α : ℝ) (L : ℕ) :
    IsProbabilityMeasure (bulkCycleVectorPoissonLaw f α L) := by
  unfold bulkCycleVectorPoissonLaw
  infer_instance
```

### bulk_cycle_point_indicator_integral

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkPointProbability.lean:33)

```lean
theorem bulk_cycle_point_indicator_integral {n : ℕ} (w : Weights n)
    (L : ℕ) (q : Fin L → ℕ) (α : ℝ) :
    (∫ z, (if (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q
      then (1 : ℝ) else 0) ∂exponentialRace w) =
      (exponentialRace w).real {z | (fun ell =>
        Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q}
```

### bulkCycleVectorPoissonLaw_real_singleton

theorem; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkPointProbability.lean:50)

```lean
theorem bulkCycleVectorPoissonLaw_real_singleton (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (L : ℕ)
    (α : ℝ) (hα : α < 1) (q : Fin L → ℕ) :
    (bulkCycleVectorPoissonLaw f α L).real {q} =
      ∏ ell, Real.exp (-bulkCycleTraceIntensity f α ell.val) *
        bulkCycleTraceIntensity f α ell.val ^ q ell / ((q ell).factorial : ℝ)
```

### bulk_cycle_point_probability_limit

theorem; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section5BulkPointProbability.lean:65)

The actual bulk cycle-vector event probabilities converge to the
unchanged independent-Poisson law determined by the manuscript integrals.

```lean
theorem bulk_cycle_point_probability_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => (exponentialRace (w n)).real {z | (fun ell =>
      Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q}) atTop
      (𝓝 ((bulkCycleVectorPoissonLaw f α L).real {q}))
```


## Luce/Section5ContractDefinitions.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractDefinitions.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### cycleTraceIntegrand

def; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractDefinitions.lean:14)

Index k denotes cycles of length k+1.

```lean
def cycleTraceIntegrand (f : ℝ → ℝ) (k : ℕ) (x : Fin (k+1) → ℝ) : ℝ :=
  ∏ a, cyclicProfileDensity f (x a) (x (finRotate (k+1) a))
```

### cycleTraceIntensity

def; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractDefinitions.lean:17)

```lean
def cycleTraceIntensity (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (1 / (k+1 : ℝ)) * ∫ x, cycleTraceIntegrand f k x ∂cyclicProfileMeasure (k+1)
```

### cycleCountVector

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractDefinitions.lean:20)

```lean
def cycleCountVector {n : ℕ} (L : ℕ) (R : Equiv.Perm (Fin n)) : Fin L → ℕ :=
  fun k => Section5.cycleCount R k.val
```

### cycleVectorPoissonLaw

def; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractDefinitions.lean:25)

The product measure means exactly independent Poisson coordinates.
Nonnegativity and finiteness of the raw intensities must be proved.

```lean
def cycleVectorPoissonLaw (f : ℝ → ℝ) (L : ℕ) : Measure (Fin L → ℕ) :=
  Measure.pi (fun k : Fin L => ProbabilityTheory.poissonMeasure (Real.toNNReal (cycleTraceIntensity f k.val)))
```

### cycleVectorTotalVariation

def; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractDefinitions.lean:29)

The same sup-over-events convention as the scalar TV definition.

```lean
def cycleVectorTotalVariation {L : ℕ} (μ ν : Measure (Fin L → ℕ)) : ℝ :=
  sSup {r : ℝ | ∃ A : Set (Fin L → ℕ), r = |μ.real A - ν.real A|}
```


## Luce/Section5ContractRepresentation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractRepresentation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce
```

### cyclicProfileMeasure_eq_closed_cube

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractRepresentation.lean:11)

The profile product measure is precisely Lebesgue measure on the
closed unit cube, since its boundary has measure zero. No profile assumption
is needed for this representation equality.

```lean
theorem cyclicProfileMeasure_eq_closed_cube (r : ℕ) :
    cyclicProfileMeasure r = volume.restrict (cyclicBulkCube r 1)
```

### cycleTraceIntensity_eq_manuscript

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractRepresentation.lean:21)

```lean
theorem cycleTraceIntensity_eq_manuscript (f : ℝ → ℝ) (k : ℕ) :
    cycleTraceIntensity f k = (1/(k+1 : ℝ)) *
      ∫ x in cyclicBulkCube (k+1) 1,
        ∏ a, cyclicProfileDensity f (x a) (x (finRotate (k+1) a))
```

### instance at line 28

instance; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractRepresentation.lean:28)

```lean
instance cycleVectorPoissonLaw_probability (f : ℝ → ℝ) (L : ℕ) :
    IsProbabilityMeasure (cycleVectorPoissonLaw f L) := by
  unfold cycleVectorPoissonLaw
  infer_instance
```

### cycleCountVector_apply

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ContractRepresentation.lean:33)

```lean
theorem cycleCountVector_apply {n : ℕ} (L : ℕ) (R : Equiv.Perm (Fin n)) (k : Fin L) :
    cycleCountVector L R k = Section5.cycleCount R k.val
```


## Luce/Section5CycleAssignments.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Function
open scoped BigOperators
namespace Luce.Section5
variable {α : Type*}
section Finite
variable [Fintype α] [DecidableEq α]
```

### CycleSlot

abbrev; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:21)

Ordered cycle slots; `ell.val+1` is the actual cycle length.

```lean
abbrev CycleSlot (L : ℕ) (m : Fin L → ℕ) := Σ ell : Fin L, Fin (m ell)
```

### CycleVertex

abbrev; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:24)

The disjoint labelled vertex set used in the factorial expansion.

```lean
abbrev CycleVertex (L : ℕ) (m : Fin L → ℕ) :=
  Σ b : CycleSlot L m, Fin (b.1.val + 1)
```

### cycleBlockPermutation

def; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:29)

The prescribed permutation sends each vertex to the next vertex of its
own directed cycle, including wraparound and singleton blocks.

```lean
def cycleBlockPermutation (L : ℕ) (m : Fin L → ℕ) : Equiv.Perm (CycleVertex L m) :=
  Equiv.sigmaCongrRight (fun b => finRotate (b.1.val + 1))
```

### CycleAssignment

abbrev; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:33)

All labelled vertices are distinct, and all prescribed edges occur in R.

```lean
abbrev CycleAssignment (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :=
  {t : CycleVertex L m ↪ α // ∀ x, R (t x) = t (cycleBlockPermutation L m x)}
```

### isRootedCycle_iff_rotate

lemma; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:36)

```lean
lemma isRootedCycle_iff_rotate (R : Equiv.Perm α) (k : ℕ) (t : Fin (k + 1) ↪ α) :
    IsRootedCycle R k t ↔ ∀ a, R (t a) = t (finRotate (k + 1) a)
```

### assignmentBlock

def; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:50)

Restrict a global assignment to one of its blocks.

```lean
def assignmentBlock {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (t : CycleAssignment R L m) (b : CycleSlot L m) : RootedCycle R b.1.val := by
  let e : Fin (b.1.val + 1) ↪ α :=
    ⟨fun a => t.1 ⟨b, a⟩, fun a c h => by
      apply Fin.ext
      exact congrArg (fun x : CycleVertex L m => x.2.val) (t.1.injective h)⟩
  refine ⟨e, (isRootedCycle_iff_rotate R b.1.val e).mpr ?_⟩
  intro a
  exact t.2 ⟨b, a⟩
```

### rootedCycle_mem_periodicOrbit_iff

lemma; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:60)

```lean
lemma rootedCycle_mem_periodicOrbit_iff {R : Equiv.Perm α} {k : ℕ}
    (t : RootedCycle R k) (y : α) :
    y ∈ periodicOrbit (R : α → α) (t.1 0) ↔ ∃ a : Fin (k + 1), t.1 a = y
```

### periodicOrbit_eq_of_mem_cycleOrbit

theorem; [source line 75](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:75)

Every vertex of an actual cycle recovers precisely that rotation class.

```lean
theorem periodicOrbit_eq_of_mem_cycleOrbit (R : Equiv.Perm α) (k : ℕ)
    (c : Cycle α) (hc : c ∈ cycleOrbits R k) (x : α) (hx : x ∈ c.toFinset) :
    periodicOrbit (R : α → α) x = c
```

### minimalPeriod_of_mem_cycleOrbit

theorem; [source line 88](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:88)

```lean
theorem minimalPeriod_of_mem_cycleOrbit (R : Equiv.Perm α) (k : ℕ)
    (c : Cycle α) (hc : c ∈ cycleOrbits R k) (x : α) (hx : x ∈ c.toFinset) :
    minimalPeriod (R : α → α) x = k + 1
```

### collectionBlock

def; [source line 95](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:95)

Enumerate the selected cycle starting at its selected root.

```lean
def collectionBlock {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : RootedCycleCollection R L m) (b : CycleSlot L m) : RootedCycle R b.1.val :=
  rootedCycleOfPeriodicPoint R b.1.val ⟨(C.2 b.1 b.2).val,
    minimalPeriod_of_mem_cycleOrbit R b.1.val _ (C.1 b.1 b.2).property _
      (C.2 b.1 b.2).property⟩
```

### collectionBlock_mem

lemma; [source line 101](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:101)

```lean
lemma collectionBlock_mem {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : RootedCycleCollection R L m) (b : CycleSlot L m) (a : Fin (b.1.val + 1)) :
    (collectionBlock C b).1 a ∈ (C.1 b.1 b.2).val.toFinset
```

### assignmentOfCollection

def; [source line 111](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:111)

Assemble all blocks into one injection. Distinct cycle slots are
vertex-disjoint by the proved permutation-cycle disjointness theorem.

```lean
def assignmentOfCollection {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : RootedCycleCollection R L m) : CycleAssignment R L m := by
  let e : CycleVertex L m ↪ α :=
    ⟨fun x => (collectionBlock C x.1).1 x.2, ?_⟩
  · refine ⟨e, ?_⟩
    intro x
    exact (isRootedCycle_iff_rotate R x.1.1.val (collectionBlock C x.1).1).mp
      (collectionBlock C x.1).2 x.2
  · intro x y he
    obtain ⟨b, a⟩ := x
    obtain ⟨c, d⟩ := y
    dsimp only at he
    by_cases hbc : b = c
    · subst c
      have had := (collectionBlock C b).1.injective he
      exact congrArg (fun a => (⟨b, a⟩ : CycleVertex L m)) had
    · have hd := C.1.disjoint b.1 c.1 b.2 c.2 hbc
      exact (Finset.disjoint_left.mp hd (collectionBlock_mem C b a)
        (he.symm ▸ collectionBlock_mem C c d)).elim
```

### collectionOfAssignment

def; [source line 133](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:133)

A global compatible injection recovers the ordered cycle classes and
their roots. Global injectivity excludes duplicate classes within a length.

```lean
def collectionOfAssignment {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (t : CycleAssignment R L m) : RootedCycleCollection R L m := by
  let C : CycleCollection R L m := fun ell =>
    ⟨fun a => ⟨periodicOrbit (R : α → α) (t.1 ⟨⟨ell, a⟩, 0⟩), by
        apply Finset.mem_image.mpr
        refine ⟨t.1 ⟨⟨ell, a⟩, 0⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          rootedCycle_minimalPeriod (assignmentBlock t ⟨ell, a⟩)⟩⟩,
      ?_⟩
  · refine ⟨C, fun ell a => ⟨t.1 ⟨⟨ell, a⟩, 0⟩, ?_⟩⟩
    change t.1 ⟨⟨ell, a⟩, 0⟩ ∈
      (periodicOrbit (R : α → α) (t.1 ⟨⟨ell, a⟩, 0⟩)).toFinset
    rw [mem_periodicOrbit_toFinset]
    exact (rootedCycle_mem_periodicOrbit_iff (assignmentBlock t ⟨ell, a⟩) _).mpr ⟨0, rfl⟩
  · intro a b hab
    have he := congrArg Subtype.val hab
    dsimp only at he
    have hb : t.1 ⟨⟨ell, b⟩, 0⟩ ∈
        periodicOrbit (R : α → α) (t.1 ⟨⟨ell, a⟩, 0⟩) := by
      rw [he]
      exact (rootedCycle_mem_periodicOrbit_iff (assignmentBlock t ⟨ell, b⟩) _).mpr ⟨0, rfl⟩
    obtain ⟨s, hs⟩ := (rootedCycle_mem_periodicOrbit_iff (assignmentBlock t ⟨ell, a⟩) _).mp hb
    apply Fin.ext
    exact congrArg (fun x : CycleVertex L m => x.1.2.val) (t.1.injective hs)
```

### assignmentOfCollection_collectionOfAssignment

theorem; [source line 158](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:158)

```lean
theorem assignmentOfCollection_collectionOfAssignment {R : Equiv.Perm α}
    {L : ℕ} {m : Fin L → ℕ} (t : CycleAssignment R L m) :
    assignmentOfCollection (collectionOfAssignment t) = t
```

### collectionOfAssignment_assignmentOfCollection

theorem; [source line 167](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:167)

```lean
theorem collectionOfAssignment_assignmentOfCollection {R : Equiv.Perm α}
    {L : ℕ} {m : Fin L → ℕ} (C : RootedCycleCollection R L m) :
    collectionOfAssignment (assignmentOfCollection C) = C
```

### rootedCollectionEquivAssignment

def; [source line 194](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:194)

The full bijection used in the factorial moment expansion: labelled,
globally distinct vertices satisfying one prescribed block permutation are
exactly ordered actual cycles with one root chosen in each cycle.

```lean
def rootedCollectionEquivAssignment (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    RootedCycleCollection R L m ≃ CycleAssignment R L m where
  toFun := assignmentOfCollection
  invFun := collectionOfAssignment
  left_inv := collectionOfAssignment_assignmentOfCollection
  right_inv := assignmentOfCollection_collectionOfAssignment
```

### cycleVertex_card

theorem; [source line 203](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:203)

The vertex domain has precisely r = sum ell*m_ell elements, without
choosing an arbitrary enumeration or changing the assignment permutation.

```lean
theorem cycleVertex_card (L : ℕ) (m : Fin L → ℕ) :
    Nat.card (CycleVertex L m) = ∑ ell : Fin L, (ell.val + 1) * m ell
```

### cycleAssignment_card

theorem; [source line 210](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:210)

Exact labelled-assignment count, with all rotational multiplicities and
falling factorials retained, including zero multiplicities and empty domains.

```lean
theorem cycleAssignment_card (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    Nat.card (CycleAssignment R L m) =
      (∏ ell : Fin L, (cycleCount R ell.val).descFactorial (m ell)) *
        ∏ ell : Fin L, (ell.val + 1) ^ m ell
```

### cycleAssignment_rootFactor_pos

theorem; [source line 219](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:219)

The rotational divisor is positive, so division cannot conceal a zero
denominator in the factorial-moment identity.

```lean
theorem cycleAssignment_rootFactor_pos (L : ℕ) (m : Fin L → ℕ) :
    0 < ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell
```

### cycle_factorial_eq_assignment_card

theorem; [source line 228](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:228)

The unrestricted deterministic factorial identity underlying source
1281–1284. The source's additional vertex cutoff is supplied by
`Section5CycleCutoff`, using this equivalence.

```lean
theorem cycle_factorial_eq_assignment_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) :
    (∏ ell : Fin L, ((cycleCount R ell.val).descFactorial (m ell) : ℝ)) =
      (Nat.card (CycleAssignment R L m) : ℝ) /
        ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell
```

### cycleBlockIndicator

def; [source line 238](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:238)

The literal product of the assignment indicators in every labelled block.

```lean
def cycleBlockIndicator (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ)
    (t : CycleVertex L m ↪ α) : ℝ :=
  ∏ x, if R (t x) = t (cycleBlockPermutation L m x) then 1 else 0
```

### sum_cycleBlockIndicator

theorem; [source line 242](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:242)

```lean
theorem sum_cycleBlockIndicator (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    (∑ t : CycleVertex L m ↪ α, cycleBlockIndicator R L m t) =
      (Nat.card (CycleAssignment R L m) : ℝ)
```

### cycle_factorial_eq_assignment_sum

theorem; [source line 252](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleAssignments.lean:252)

The unrestricted expansion into distinct labelled assignment indicators,
with exactly the product of rotational divisors. The cutoff expansion used
by the source is proved in `Section5CycleCutoff`.

```lean
theorem cycle_factorial_eq_assignment_sum (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) :
    (∏ ell : Fin L, ((cycleCount R ell.val).descFactorial (m ell) : ℝ)) =
      (∑ t : CycleVertex L m ↪ α, cycleBlockIndicator R L m t) /
        ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell
```


## Luce/Section5CycleCutoff.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Function
open scoped BigOperators
namespace Luce.Section5
variable {α : Type*} [Fintype α] [DecidableEq α]
```

### CycleCollectionWithin

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:21)

Every vertex of every selected cycle belongs to the cutoff.

```lean
def CycleCollectionWithin {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (S : Finset α) (C : CycleCollection R L m) : Prop :=
  ∀ ell a, (C ell a).val.toFinset ⊆ S
```

### RootedCycleCollectionWithin

abbrev; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:25)

```lean
abbrev RootedCycleCollectionWithin (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :=
  {C : RootedCycleCollection R L m // CycleCollectionWithin S C.1}
```

### CycleAssignmentWithin

abbrev; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:29)

```lean
abbrev CycleAssignmentWithin (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :=
  {t : CycleAssignment R L m // ∀ x, t.1 x ∈ S}
```

### collectionWithin_iff_assignmentWithin

theorem; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:35)

The root enumeration covers the whole cycle, so imposing the cutoff on
labels is equivalent to imposing it on all vertices of each selected cycle.

```lean
theorem collectionWithin_iff_assignmentWithin {R : Equiv.Perm α}
    {L : ℕ} {m : Fin L → ℕ} (S : Finset α) (C : RootedCycleCollection R L m) :
    CycleCollectionWithin S C.1 ↔ ∀ x, (assignmentOfCollection C).1 x ∈ S
```

### rootedCollectionWithinEquivAssignmentWithin

def; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:54)

The full labelled-cycle bijection restricts to any cutoff set, including
the empty set, even when the cutoff is not invariant under R.

```lean
def rootedCollectionWithinEquivAssignmentWithin (R : Equiv.Perm α)
    (L : ℕ) (m : Fin L → ℕ) (S : Finset α) :
    RootedCycleCollectionWithin R L m S ≃ CycleAssignmentWithin R L m S :=
  (rootedCollectionEquivAssignment R L m).subtypeEquiv
    (collectionWithin_iff_assignmentWithin S)
```

### cycleOrbitsWithin

def; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:61)

Actual permutation cycles of length k+1 all of whose vertices lie in S.

```lean
def cycleOrbitsWithin (R : Equiv.Perm α) (S : Finset α) (k : ℕ) : Finset (Cycle α) := by
  classical
  exact (cycleOrbits R k).filter (fun c => c.toFinset ⊆ S)
```

### cycleCountWithin

def; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:65)

```lean
def cycleCountWithin (R : Equiv.Perm α) (S : Finset α) (k : ℕ) : ℕ :=
  (cycleOrbitsWithin R S k).card
```

### cycleCountWithin_univ

theorem; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:68)

```lean
theorem cycleCountWithin_univ (R : Equiv.Perm α) (k : ℕ) :
    cycleCountWithin R Finset.univ k = cycleCount R k
```

### CutoffCycleCollection

abbrev; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:73)

Ordered distinct cycles selected directly from the cutoff cycle set.

```lean
abbrev CutoffCycleCollection (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :=
  (ell : Fin L) → (Fin (m ell) ↪ ↥(cycleOrbitsWithin R S ell.val))
```

### collectionWithinEquivCutoffCollection

def; [source line 79](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:79)

Restricting the ambient collection and selecting from the filtered cycle
set are exactly equivalent, without strengthening the cutoff condition.

```lean
def collectionWithinEquivCutoffCollection (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    {C : CycleCollection R L m // CycleCollectionWithin S C} ≃
      CutoffCycleCollection R L m S where
  toFun C ell :=
    ⟨fun a => ⟨(C.1 ell a).val, Finset.mem_filter.mpr ⟨(C.1 ell a).property, C.2 ell a⟩⟩,
      fun a b h => (C.1 ell).injective
        (Subtype.ext (congrArg (fun c : ↥(cycleOrbitsWithin R S ell.val) => c.val) h))⟩
  invFun C :=
    ⟨fun ell => ⟨fun a => ⟨(C ell a).val, (Finset.mem_filter.mp (C ell a).property).1⟩,
      fun a b h => (C ell).injective
        (Subtype.ext (congrArg (fun c : ↥(cycleOrbits R ell.val) => c.val) h))⟩,
      fun ell a => (Finset.mem_filter.mp (C ell a).property).2⟩
  left_inv C := by
    apply Subtype.ext
    funext ell
    apply Function.Embedding.ext
    intro a
    rfl
  right_inv C := by
    funext ell
    apply Function.Embedding.ext
    intro a
    rfl
```

### cutoffCycleCollection_card

theorem; [source line 104](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:104)

```lean
theorem cutoffCycleCollection_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    Nat.card (CutoffCycleCollection R L m S) =
      ∏ ell : Fin L, (cycleCountWithin R S ell.val).descFactorial (m ell)
```

### collectionWithin_card

theorem; [source line 112](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:112)

```lean
theorem collectionWithin_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    Nat.card {C : CycleCollection R L m // CycleCollectionWithin S C} =
      ∏ ell : Fin L, (cycleCountWithin R S ell.val).descFactorial (m ell)
```

### rootedCycleCollectionWithin_card

theorem; [source line 121](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:121)

Restricting a cycle collection does not alter its number of roots: every
selected cycle retains all of its length-many vertices.

```lean
theorem rootedCycleCollectionWithin_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    Nat.card (RootedCycleCollectionWithin R L m S) =
      (∏ ell : Fin L, (cycleCountWithin R S ell.val).descFactorial (m ell)) *
        ∏ ell : Fin L, (ell.val + 1) ^ m ell
```

### cycleAssignmentWithin_card

theorem; [source line 140](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:140)

The cutoff-compatible global injection has exactly the requested falling
factorial count times the original rotational multiplicity.

```lean
theorem cycleAssignmentWithin_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    Nat.card (CycleAssignmentWithin R L m S) =
      (∏ ell : Fin L, (cycleCountWithin R S ell.val).descFactorial (m ell)) *
        ∏ ell : Fin L, (ell.val + 1) ^ m ell
```

### cutoff_cycle_factorial_eq_assignment_card

theorem; [source line 148](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:148)

```lean
theorem cutoff_cycle_factorial_eq_assignment_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    (∏ ell : Fin L, ((cycleCountWithin R S ell.val).descFactorial (m ell) : ℝ)) =
      (Nat.card (CycleAssignmentWithin R L m S) : ℝ) /
        ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell
```

### cycleBlockIndicatorWithin

def; [source line 159](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:159)

The cutoff restriction is imposed on every labelled vertex, as in the
paper's sum over distinct bulk indices.

```lean
def cycleBlockIndicatorWithin (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ)
    (S : Finset α) (t : CycleVertex L m ↪ α) : ℝ := by
  classical
  exact if ∀ x, t x ∈ S then cycleBlockIndicator R L m t else 0
```

### sum_cycleBlockIndicatorWithin

theorem; [source line 164](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:164)

```lean
theorem sum_cycleBlockIndicatorWithin (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    (∑ t : CycleVertex L m ↪ α, cycleBlockIndicatorWithin R L m S t) =
      (Nat.card (CycleAssignmentWithin R L m S) : ℝ)
```

### cutoff_cycle_factorial_eq_assignment_sum

theorem; [source line 190](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:190)

The exact deterministic factorial expansion at source 1281–1284 for
cycles wholly inside an arbitrary cutoff. All labels are distinct, edge
orientations are the prescribed block rotations, and every rotation factor
is retained. Empty cutoffs and zero multiplicities require no exceptions.

```lean
theorem cutoff_cycle_factorial_eq_assignment_sum (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    (∏ ell : Fin L, ((cycleCountWithin R S ell.val).descFactorial (m ell) : ℝ)) =
      (∑ t : CycleVertex L m ↪ α, cycleBlockIndicatorWithin R L m S t) /
        ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell
```

### bulkCycleLabelSet

def; [source line 199](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:199)

The paper's bulk labels are one-based; `Fin n` stores label i as i-1.

```lean
def bulkCycleLabelSet (n : ℕ) (a : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i.val : ℝ) + 1 ≤ a * n)
```

### bulkCycleCount

def; [source line 202](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:202)

```lean
def bulkCycleCount {n : ℕ} (R : Equiv.Perm (Fin n)) (a : ℝ) (k : ℕ) : ℕ :=
  cycleCountWithin R (bulkCycleLabelSet n a) k
```

### bulk_cycle_factorial_eq_assignment_sum

theorem; [source line 208](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleCutoff.lean:208)

Literal source instantiation: the cycle count C^(a) counts only cycles
whose one-based labels are at most a*n. The displayed summation condition
imposes that same bound on every vertex of the global injection.

```lean
theorem bulk_cycle_factorial_eq_assignment_sum {n : ℕ}
    (R : Equiv.Perm (Fin n)) (L : ℕ) (m : Fin L → ℕ) (a : ℝ) :
    (∏ ell : Fin L, ((bulkCycleCount R a ell.val).descFactorial (m ell) : ℝ)) =
      (∑ t : CycleVertex L m ↪ Fin n,
        if ∀ x, ((t x).val : ℝ) + 1 ≤ a * n then cycleBlockIndicator R L m t else 0) /
        ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell
```


## Luce/Section5CycleProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce
```

### raceRankPermutation

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:21)

Total rank permutation. On the null set of tied clock configurations
it is extended by the identity; on distinct clocks it is the actual rank map.

```lean
def raceRankPermutation {n : ℕ} (clocks : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  if h : Function.Injective clocks then rankPermutation clocks h else Equiv.refl _
```

### raceRankPermutation_eq

lemma; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:24)

```lean
lemma raceRankPermutation_eq {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) :
    raceRankPermutation clocks = rankPermutation clocks hinj
```

### section5_measurableSet_injective_clocks

lemma; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:29)

```lean
lemma section5_measurableSet_injective_clocks (n : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ | Function.Injective clocks}
```

### measurable_raceRankPermutation_apply

lemma; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:45)

```lean
lemma measurable_raceRankPermutation_apply {n : ℕ} (i : Fin n) :
    Measurable (fun clocks : Fin n → ℝ => raceRankPermutation clocks i)
```

### measurable_raceRankPermutation_function

lemma; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:68)

```lean
lemma measurable_raceRankPermutation_function {n : ℕ} :
    Measurable (fun clocks : Fin n → ℝ => (raceRankPermutation clocks : Fin n → Fin n))
```

### measurableSet_cycle_period

lemma; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:72)

```lean
lemma measurableSet_cycle_period {n : ℕ} (v : Fin n) (k : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1}
```

### exists_cycle_tail_of_minimalPeriod

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:81)

A vertex with minimal period `k+1` has a directed tuple with that root,
with `k` distinct remaining vertices avoiding it. The endpoint is the root.

```lean
theorem exists_cycle_tail_of_minimalPeriod {n k : ℕ} (R : Equiv.Perm (Fin n))
    (v : Fin n) (hperiod : minimalPeriod (R : Fin n → Fin n) v = k + 1) :
    ∃ u : Fin k → Fin n, Function.Injective u ∧ (∀ a, u a ≠ v) ∧
      ∀ a : Fin (k + 1), R ((Fin.cons v u : Fin (k + 1) → Fin n) a) =
        (Fin.snoc u v : Fin (k + 1) → Fin n) a
```

### cycle_period_has_rankCylinder

theorem; [source line 110](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:110)

On distinct clock configurations, the cycle tuple satisfies the exact
one-based rank assignments required by the ghost cylinder inequality.

```lean
theorem cycle_period_has_rankCylinder {n k : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (v : Fin n)
    (hperiod : minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1) :
    ∃ u : Fin k → Fin n, Function.Injective u ∧ (∀ a, u a ≠ v) ∧
      MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks
```

### cycle_period_probability_le_sum_cylinders

theorem; [source line 129](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:129)

The cycle event is covered by precisely the admissible rooted cylinders.
The finite union bound introduces no rotation or factorial multiplicity.

```lean
theorem cycle_period_probability_le_sum_cylinders {n k : ℕ} (w : Weights n)
    (v : Fin n) :
    exponentialRace w {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1} ≤
      ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        exponentialRace w {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks}
```

### cycle_period_real_probability_le_sum_cylinders

lemma; [source line 150](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:150)

```lean
lemma cycle_period_real_probability_le_sum_cylinders {n k : ℕ} (w : Weights n)
    (v : Fin n) :
    (exponentialRace w).real {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1} ≤
      ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        (exponentialRace w).real
          {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks}
```

### ghostCycleVertexSum

def; [source line 169](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:169)

The source's rooted cycle sum: first edge out of `v`, followed by a
distinct-source path ending at `v`. For `k=0` this is exactly `p_(v,v)`.

```lean
def ghostCycleVertexSum {n : ℕ} (w : Weights n) (k : ℕ)
    (v : Fin n) (old : Fin n → ℝ) : ℝ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
      Function.Injective u ∧ ∀ a, u a ≠ v),
    ghostEntry w (k + 1) old v ((Fin.snoc u v : Fin (k + 1) → Fin n) 0) *
      ∏ a : Fin k, ghostEntry w (k + 1) old (u a)
        ((Fin.snoc u v : Fin (k + 1) → Fin n) a.succ)
```

### ghostCycleVertexSum_eq_cylinder_sum

lemma; [source line 177](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:177)

```lean
lemma ghostCycleVertexSum_eq_cylinder_sum {n : ℕ} (w : Weights n) (k : ℕ)
    (v : Fin n) (old : Fin n → ℝ) :
    ghostCycleVertexSum w k v old =
      ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        ∏ a : Fin (k + 1), ghostEntry w (k + 1) old
          ((Fin.cons v u : Fin (k + 1) → Fin n) a)
          ((Fin.snoc u v : Fin (k + 1) → Fin n) a)
```

### ghostCycleVertexSum_integrable

theorem; [source line 189](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:189)

Every cycle-probability majorant is integrable before its expectation
is used. Its finitely many summands are products of probabilities.

```lean
theorem ghostCycleVertexSum_integrable {n : ℕ} (w : Weights n) (k : ℕ)
    (v : Fin n) : Integrable (ghostCycleVertexSum w k v) (exponentialRace w)
```

### cycle_vertex_probability_le_ghost

theorem; [source line 200](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleProbability.lean:200)

The exact finite vertex-cycle comparison used in the high- and low-rate
proofs: the cycle probability is bounded by the expected rooted ghost sum.
There is no symmetry factor because the root is fixed.

```lean
theorem cycle_vertex_probability_le_ghost {n : ℕ} (w : Weights n) (k : ℕ)
    (v : Fin n) :
    (exponentialRace w).real {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1} ≤
      ∫ old, ghostCycleVertexSum w k v old ∂exponentialRace w
```


## Luce/Section5Cycles.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean)

Namespace / shared context (consult source for section boundaries):

```lean
namespace Luce.Section5
open Function
variable {α : Type*}
section Counting
variable [Fintype α] [DecidableEq α]
```

### IsRootedCycle

def; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:25)

The closed directed assignment in equation (cycle-counts), with a root.

```lean
def IsRootedCycle (R : Equiv.Perm α) (k : ℕ) (t : Fin (k + 1) ↪ α) : Prop :=
  (∀ a : Fin k, R (t a.castSucc) = t a.succ) ∧ R (t (Fin.last k)) = t 0
```

### instance at line 28

instance; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:28)

```lean
instance [DecidableEq α] (R : Equiv.Perm α) (k : ℕ) (t : Fin (k + 1) ↪ α) :
    Decidable (IsRootedCycle R k t) :=
  inferInstanceAs (Decidable
    ((∀ a : Fin k, R (t a.castSucc) = t a.succ) ∧ R (t (Fin.last k)) = t 0))
```

### RootedCycle

abbrev; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:34)

A tuple of distinct labels satisfying all the cycle assignments.

```lean
abbrev RootedCycle (R : Equiv.Perm α) (k : ℕ) :=
  {t : Fin (k + 1) ↪ α // IsRootedCycle R k t}
```

### rootedCycle_eq_iterate

theorem; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:38)

The directed assignments determine every entry from the chosen root.

```lean
theorem rootedCycle_eq_iterate {R : Equiv.Perm α} {k : ℕ}
    (t : RootedCycle R k) (a : Fin (k + 1)) :
    t.1 a = (R : α → α)^[a.val] (t.1 0)
```

### rootedCycle_isPeriodicPt

theorem; [source line 47](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:47)

```lean
theorem rootedCycle_isPeriodicPt {R : Equiv.Perm α} {k : ℕ}
    (t : RootedCycle R k) :
    IsPeriodicPt (R : α → α) (k + 1) (t.1 0)
```

### rootedCycle_minimalPeriod

theorem; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:59)

Distinctness excludes every smaller positive period; no proper divisor
is counted as a cycle of length `k + 1`.

```lean
theorem rootedCycle_minimalPeriod {R : Equiv.Perm α} {k : ℕ}
    (t : RootedCycle R k) :
    minimalPeriod (R : α → α) (t.1 0) = k + 1
```

### rootedCycleOfPeriodicPoint

def; [source line 77](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:77)

Enumerate the actual orbit of a point of minimal period `k + 1`.

```lean
noncomputable def rootedCycleOfPeriodicPoint (R : Equiv.Perm α) (k : ℕ)
    (x : {x : α // minimalPeriod (R : α → α) x = k + 1}) : RootedCycle R k := by
  refine ⟨⟨fun a => (R : α → α)^[a.val] x.1, ?_⟩, ?_, ?_⟩
  · intro a b hab
    apply Fin.ext
    exact iterate_injOn_Iio_minimalPeriod (by simpa [x.2] using a.isLt)
      (by simpa [x.2] using b.isLt) hab
  · intro a
    exact (Function.iterate_succ_apply' _ _ _).symm
  · change R ((R : α → α)^[k] x.1) = x.1
    rw [← Function.iterate_succ_apply' (R : α → α) k x.1]
    simpa only [x.2] using (iterate_minimalPeriod (f := (R : α → α)) (x := x.1))
```

### rootedCycleEquivPeriodicPoint

def; [source line 92](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:92)

The exact correspondence between the paper's directed tuples and vertices
in cycles of the specified length (`fixed_points.tex:164–170, 303–304`).

```lean
noncomputable def rootedCycleEquivPeriodicPoint (R : Equiv.Perm α) (k : ℕ) :
    RootedCycle R k ≃ {x : α // minimalPeriod (R : α → α) x = k + 1} where
  toFun t := ⟨t.1 0, rootedCycle_minimalPeriod t⟩
  invFun := rootedCycleOfPeriodicPoint R k
  left_inv t := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro a
    exact (rootedCycle_eq_iterate t a).symm
  right_inv x := by
    apply Subtype.ext
    rfl
```

### cycleVertices

def; [source line 110](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:110)

The vertices whose actual orbit has the specified positive length.

```lean
noncomputable def cycleVertices (R : Equiv.Perm α) (k : ℕ) : Finset α := by
  classical
  exact Finset.univ.filter (fun x => minimalPeriod (R : α → α) x = k + 1)
```

### cycleOrbits

def; [source line 115](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:115)

Actual directed cycles, as mathlib's lists modulo rotation.

```lean
noncomputable def cycleOrbits (R : Equiv.Perm α) (k : ℕ) : Finset (Cycle α) := by
  classical
  exact (cycleVertices R k).image (periodicOrbit (R : α → α))
```

### cycleCount

def; [source line 120](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:120)

Number of unrooted cycles, including singleton fixed points.

```lean
noncomputable def cycleCount (R : Equiv.Perm α) (k : ℕ) : ℕ :=
  (cycleOrbits R k).card

omit [Fintype α] in
```

### mem_periodicOrbit_toFinset

theorem; [source line 124](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:124)

```lean
theorem mem_periodicOrbit_toFinset (R : Equiv.Perm α) (x y : α) :
    y ∈ (periodicOrbit (R : α → α) x).toFinset ↔
      y ∈ periodicOrbit (R : α → α) x
```

### periodicOrbit_toFinset_card

theorem; [source line 130](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:130)

```lean
theorem periodicOrbit_toFinset_card (R : Equiv.Perm α) (x : α) :
    (periodicOrbit (R : α → α) x).toFinset.card = minimalPeriod (R : α → α) x
```

### cycleOrbit_fiber

theorem; [source line 139](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:139)

Exactly the vertices of one orbit give that rotation class.

```lean
theorem cycleOrbit_fiber (R : Equiv.Perm α) (k : ℕ) (x : α)
    (hx : minimalPeriod (R : α → α) x = k + 1) :
    ((cycleVertices R k).filter (fun y =>
      periodicOrbit (R : α → α) y = periodicOrbit (R : α → α) x)) =
      (periodicOrbit (R : α → α) x).toFinset
```

### cycleVertices_card

theorem; [source line 163](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:163)

Each cycle has exactly `k + 1` possible roots. This proves the symmetry
factor asserted at `fixed_points.tex:303–304`; no factorial is omitted.

```lean
theorem cycleVertices_card (R : Equiv.Perm α) (k : ℕ) :
    (cycleVertices R k).card = (k + 1) * cycleCount R k
```

### rootedCycle_card

theorem; [source line 180](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:180)

Rooted tuples count vertices rather than unrooted cycles.

```lean
theorem rootedCycle_card (R : Equiv.Perm α) (k : ℕ) :
    Nat.card (RootedCycle R k) = (k + 1) * cycleCount R k
```

### cycleAssignmentWeight

def; [source line 188](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:188)

The product of the directed edge indicators in equation (cycle-counts).

```lean
noncomputable def cycleAssignmentWeight (R : Equiv.Perm α) (k : ℕ)
    (t : Fin (k + 1) ↪ α) : ℝ :=
  (∏ a : Fin k, if R (t a.castSucc) = t a.succ then 1 else 0) *
    (if R (t (Fin.last k)) = t 0 then 1 else 0)

omit [Fintype α] in
```

### cycleAssignmentWeight_eq_indicator

theorem; [source line 194](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:194)

```lean
theorem cycleAssignmentWeight_eq_indicator (R : Equiv.Perm α) (k : ℕ)
    (t : Fin (k + 1) ↪ α) :
    cycleAssignmentWeight R k t = if IsRootedCycle R k t then 1 else 0
```

### sum_cycleAssignmentWeight

theorem; [source line 203](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:203)

The full distinct-tuple sum in the paper really is the number of roots.

```lean
theorem sum_cycleAssignmentWeight (R : Equiv.Perm α) (k : ℕ) :
    (∑ t : Fin (k + 1) ↪ α, cycleAssignmentWeight R k t) =
      (Nat.card (RootedCycle R k) : ℝ)
```

### cycleCount_eq_div_rootedCycle_card

theorem; [source line 212](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:212)

The paper's positive divisor is legitimate, and recovers the integer
number of cycles from the directed-tuple count.

```lean
theorem cycleCount_eq_div_rootedCycle_card (R : Equiv.Perm α) (k : ℕ) :
    (cycleCount R k : ℝ) =
      (1 / (k + 1 : ℝ)) * (Nat.card (RootedCycle R k) : ℝ)
```

### cycleCount_eq_tuple_sum

theorem; [source line 222](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:222)

Exact source-to-Lean correspondence for equation (cycle-counts), including
the factor `1 / (k + 1)` and the singleton case.

```lean
theorem cycleCount_eq_tuple_sum (R : Equiv.Perm α) (k : ℕ) :
    (cycleCount R k : ℝ) = (1 / (k + 1 : ℝ)) *
      ∑ t : Fin (k + 1) ↪ α, cycleAssignmentWeight R k t
```

### minimalPeriod_symm

theorem; [source line 228](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:228)

```lean
theorem minimalPeriod_symm (R : Equiv.Perm α) (x : α) :
    minimalPeriod (R.symm : α → α) x = minimalPeriod (R : α → α) x
```

### cycleCount_symm

theorem; [source line 240](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:240)

The draw order and rank permutation have the same cycle counts, as stated
at `fixed_points.tex:171–172`; inversion reverses the directed edges.

```lean
theorem cycleCount_symm (R : Equiv.Perm α) (k : ℕ) :
    cycleCount R.symm k = cycleCount R k
```

### cycleCount_zero

theorem; [source line 249](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:249)

Length one is exactly the fixed-point count, including empty permutations.

```lean
theorem cycleCount_zero (R : Equiv.Perm α) :
    cycleCount R 0 = (Finset.univ.filter (fun x => R x = x)).card
```

### cycleCount_eq_fixedCount

theorem; [source line 254](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:254)

```lean
theorem cycleCount_eq_fixedCount {n : ℕ} (R : Equiv.Perm (Fin n)) :
    cycleCount R 0 = Luce.fixedCount R
```

### cycleCount_eq_zero_of_card_lt

theorem; [source line 259](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:259)

Cycles longer than the ambient permutation do not exist.

```lean
theorem cycleCount_eq_zero_of_card_lt (R : Equiv.Perm α) (k : ℕ)
    (hk : Fintype.card α < k + 1) : cycleCount R k = 0
```

### cycleOrbit_length

theorem; [source line 272](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:272)

```lean
theorem cycleOrbit_length (R : Equiv.Perm α) (k : ℕ) (c : Cycle α)
    (hc : c ∈ cycleOrbits R k) : c.length = k + 1
```

### cycleOrbit_card

theorem; [source line 278](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:278)

```lean
theorem cycleOrbit_card (R : Equiv.Perm α) (k : ℕ) (c : Cycle α)
    (hc : c ∈ cycleOrbits R k) : c.toFinset.card = k + 1
```

### cycleOrbits_disjoint

theorem; [source line 286](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:286)

Distinct actual permutation cycles have no common vertex, the essential
disjointness in the factorial expansion at `fixed_points.tex:1281–1284`.

```lean
theorem cycleOrbits_disjoint (R : Equiv.Perm α) (k j : ℕ) (c d : Cycle α)
    (hc : c ∈ cycleOrbits R k) (hd : d ∈ cycleOrbits R j) (hne : c ≠ d) :
    Disjoint c.toFinset d.toFinset
```

### CycleCollection

abbrev; [source line 315](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:315)

For each length, an ordered list of pairwise different actual cycles.
`m = 0` gives the empty list, as required for falling factorial moments.

```lean
abbrev CycleCollection (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :=
  (ℓ : Fin L) → (Fin (m ℓ) ↪ ↥(cycleOrbits R ℓ.val))
```

### cycleCollection_card

theorem; [source line 320](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:320)

The joint falling factorial counts exactly ordered collections of cycles.
This is the first equality in the expansion at `fixed_points.tex:1281–1284`.

```lean
theorem cycleCollection_card (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    Nat.card (CycleCollection R L m) =
      ∏ ℓ : Fin L, (cycleCount R ℓ.val).descFactorial (m ℓ)
```

### CycleCollection.distinct

theorem; [source line 329](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:329)

Cycles selected by different slots of an ordered collection are distinct,
also when their lengths differ.

```lean
theorem CycleCollection.distinct {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : CycleCollection R L m) (ℓ j : Fin L) (a : Fin (m ℓ)) (b : Fin (m j))
    (hne : (⟨ℓ, a⟩ : Σ i : Fin L, Fin (m i)) ≠ ⟨j, b⟩) :
    (C ℓ a).val ≠ (C j b).val
```

### CycleCollection.disjoint

theorem; [source line 347](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:347)

Thus every collection counted by the joint falling factorial is genuinely
vertex-disjoint; injectivity restrictions have not been dropped.

```lean
theorem CycleCollection.disjoint {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : CycleCollection R L m) (ℓ j : Fin L) (a : Fin (m ℓ)) (b : Fin (m j))
    (hne : (⟨ℓ, a⟩ : Σ i : Fin L, Fin (m i)) ≠ ⟨j, b⟩) :
    Disjoint (C ℓ a).val.toFinset (C j b).val.toFinset
```

### CycleRoots

abbrev; [source line 355](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:355)

One chosen vertex, or root, in every cycle in a collection.

```lean
abbrev CycleRoots {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : CycleCollection R L m) :=
  (ℓ : Fin L) → (a : Fin (m ℓ)) → ↥((C ℓ a).val.toFinset)
```

### cycleRoots_card

theorem; [source line 361](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:361)

Rooting an ordered collection has precisely the paper's product of
rotation factors, even when some multiplicities or `L` are zero.

```lean
theorem cycleRoots_card {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : CycleCollection R L m) :
    Nat.card (CycleRoots C) = ∏ ℓ : Fin L, (ℓ.val + 1) ^ m ℓ
```

### RootedCycleCollection

abbrev; [source line 378](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:378)

An ordered cycle collection together with one root in each cycle.

```lean
abbrev RootedCycleCollection (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :=
  Σ C : CycleCollection R L m, CycleRoots C
```

### rootedCycleCollection_card

theorem; [source line 383](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean:383)

The full root multiplicity in the joint factorial expansion: the factor
is `∏ ell, ell ^ m_ell`, with no additional factorial from ordering cycles.

```lean
theorem rootedCycleCollection_card (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    Nat.card (RootedCycleCollection R L m) =
      (∏ ℓ : Fin L, (cycleCount R ℓ.val).descFactorial (m ℓ)) *
        ∏ ℓ : Fin L, (ℓ.val + 1) ^ m ℓ
```


## Luce/Section5CycleShellContract.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellContract.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Luce MeasureTheory Filter
open scoped BigOperators Topology
namespace ShellMigrationContract
```

### cycleShell

def; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellContract.lean:12)

```lean
def cycleShell : Prop :=
  ∀ (w : WeightArray) (f : ℝ → ℝ), NormalizedWeights w → ProfileLimit w f →
    EndpointShellAssumption w → ∀ L : ℕ,
      Tendsto (fun α : ℝ => limsup (fun n : ℕ =>
        ∫ e, (∑ k : Fin L, (Section5.cycleCount (raceRankPermutation e) k.val -
          Section5.bulkCycleCount (raceRankPermutation e) α k.val : ℕ) : ℝ)
          ∂exponentialRace (w n)) atTop) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```


## Luce/Section5CycleShellContractCheck.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellContractCheck.lean)

### cycleShell_contractCheck

theorem; [source line 5](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellContractCheck.lean:5)

Closed kernel-checked milestone; no parameters outside the contract.

```lean
theorem cycleShell_contractCheck : ShellMigrationContract.cycleShell
```


## Luce/Section5CycleShellTightness.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellTightness.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
```

### shortCycleTailExpectation

def; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellTightness.lean:8)

```lean
def shortCycleTailExpectation (w : WeightArray) (L n : ℕ) (α : ℝ) : ℝ :=
  ∑ k : Fin L, cycleTailExpectation w k.val n α
```

### shortCycleTailExpectation_eq_integral

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellTightness.lean:11)

```lean
theorem shortCycleTailExpectation_eq_integral (w : WeightArray) (L n : ℕ) (α : ℝ) :
    shortCycleTailExpectation w L n α =
      ∫ e, (∑ k : Fin L, (Section5.cycleCount (raceRankPermutation e) k.val -
        Section5.bulkCycleCount (raceRankPermutation e) α k.val : ℕ) : ℝ)
        ∂exponentialRace (w n)
```

### shortCycleTailExpectation_nonneg

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellTightness.lean:19)

```lean
theorem shortCycleTailExpectation_nonneg (w : WeightArray) (L n : ℕ) (α : ℝ) :
    0 ≤ shortCycleTailExpectation w L n α
```

### shortCycleTailExpectation_antitone

theorem; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellTightness.lean:23)

```lean
theorem shortCycleTailExpectation_antitone (w : WeightArray) (L n : ℕ) :
    Antitone (shortCycleTailExpectation w L n)
```

### EndpointShellAssumption.short_cycle_tail_small

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellTightness.lean:28)

```lean
theorem EndpointShellAssumption.short_cycle_tail_small {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, α < 1 ∧ ∀ᶠ n : ℕ in atTop, shortCycleTailExpectation w L n α < ε
```

### EndpointShellAssumption.cycle_shell_tightness

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleShellTightness.lean:56)

The revised manuscript's complete short-cycle endpoint expectation
limit. Its only model hypotheses are normalization, profile convergence,
and the exact raw endpoint shell condition.

```lean
theorem EndpointShellAssumption.cycle_shell_tightness {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) :
    Tendsto (fun α : ℝ => limsup (fun n : ℕ =>
      ∫ e, (∑ k : Fin L, (Section5.cycleCount (raceRankPermutation e) k.val -
        Section5.bulkCycleCount (raceRankPermutation e) α k.val : ℕ) : ℝ)
        ∂exponentialRace (w n)) atTop) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```


## Luce/Section5CycleTailLimit.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleTailLimit.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce
```

### cycleTailExpectation

def; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleTailLimit.lean:8)

```lean
def cycleTailExpectation (w : WeightArray) (k n : ℕ) (α : ℝ) : ℝ :=
  ∫ e, ((Section5.cycleCount (raceRankPermutation e) k -
    Section5.bulkCycleCount (raceRankPermutation e) α k : ℕ) : ℝ) ∂exponentialRace (w n)
```

### cycleTailExpectation_nonneg

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleTailLimit.lean:12)

```lean
theorem cycleTailExpectation_nonneg (w : WeightArray) (k n : ℕ) (α : ℝ) :
    0 ≤ cycleTailExpectation w k n α
```

### cycleTailExpectation_antitone

theorem; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleTailLimit.lean:15)

```lean
theorem cycleTailExpectation_antitone (w : WeightArray) (k n : ℕ) :
    Antitone (cycleTailExpectation w k n)
```

### cycleTailExpectation_limit_of_small

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleTailLimit.lean:33)

A real limsup is used only after proving the relevant row sequence
eventually bounded above and nonnegative.

```lean
theorem cycleTailExpectation_limit_of_small (w : WeightArray) (k : ℕ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, α < 1 ∧
      ∀ᶠ n in atTop, cycleTailExpectation w k n α < ε) :
    Tendsto (fun α : ℝ => limsup (fun n => cycleTailExpectation w k n α) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```

### EndpointShellAssumption.cycle_tail_limit_succ

theorem; [source line 57](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleTailLimit.lean:57)

```lean
theorem EndpointShellAssumption.cycle_tail_limit_succ {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (k : ℕ) :
    Tendsto (fun α : ℝ => limsup (fun n => cycleTailExpectation w (k+1) n α) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```


## Luce/Section5CycleTailSmall.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleTailSmall.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce
```

### EndpointShellAssumption.cycle_tail_small_succ

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CycleTailSmall.lean:11)

Full endpoint expectation control for each cycle length at least two.
The high-rate cutoff is chosen first, then the source/interior cutoff,
then delta, then the target cutoff, all before the eventual row.

```lean
theorem EndpointShellAssumption.cycle_tail_small_succ {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, α < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (∫ e, ((Section5.cycleCount (raceRankPermutation e) (k+1) -
        Section5.bulkCycleCount (raceRankPermutation e) α (k+1) : ℕ) : ℝ)
        ∂exponentialRace (w n)) < ε
```


## Luce/Section5CyclicAnalytic.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set Function
open scoped Topology BigOperators
namespace Luce
```

### cyclicProfileDensity

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:21)

The density rho, with source coordinate first and target rank second.

```lean
def cyclicProfileDensity (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  rateKernel (profileQuantile profileMeasure f y) (f x) /
    profileD profileMeasure f (profileQuantile profileMeasure f y)
```

### cyclicProfileMeasure

def; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:25)

```lean
def cyclicProfileMeasure (r : ℕ) : Measure (Fin r → ℝ) :=
  Measure.pi (fun _ : Fin r => profileMeasure)
```

### instance at line 28

instance; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:28)

```lean
instance (r : ℕ) : IsProbabilityMeasure (cyclicProfileMeasure r) := by
  unfold cyclicProfileMeasure
  infer_instance
```

### cyclicBulkCube

def; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:32)

```lean
def cyclicBulkCube (r : ℕ) (α : ℝ) : Set (Fin r → ℝ) :=
  Set.pi Set.univ (fun _ => Icc (0 : ℝ) α)
```

### cyclicBulkInterior

def; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:35)

```lean
def cyclicBulkInterior (r : ℕ) (α : ℝ) : Set (Fin r → ℝ) :=
  Set.pi Set.univ (fun _ => Ioc (0 : ℝ) α)
```

### cyclicRaceSum

def; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:40)

The signed finite cyclic sum of Lemma 5.2 in the original row n.
Injectivity is global and the race rank and target labels are one-based.

```lean
def cyclicRaceSum {n r : ℕ} (w : Weights n) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) : ℝ := by
  classical
  exact ∑ i : Fin r ↪ Fin n,
    if ∀ a, ((i a).val : ℝ) + 1 ≤ α * n then
      g (fun a => ((i a).val + 1 : ℝ) / n) *
        (exponentialRace w).real
          {E | ∀ a, raceRank E (i a) = (i (τ a)).val + 1}
    else 0
```

### cyclicProfileIntegral

def; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:50)

```lean
def cyclicProfileIntegral {r : ℕ} (f : ℝ → ℝ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) : ℝ :=
  ∫ x in cyclicBulkInterior r α,
    g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a)) ∂cyclicProfileMeasure r
```

### cyclicGridKernel

def; [source line 57](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:57)

The coefficient G includes the signed test function and the product of
reciprocal denominators. Its continuity will be derived from those objects.

```lean
def cyclicGridKernel {r : ℕ} (n : ℕ) (α : ℝ) (τ : Equiv.Perm (Fin r))
    (G : (Fin r → ℝ) → ℝ) (t f : ℝ → ℝ) (x : Fin r → ℝ) : ℝ := by
  classical
  exact if ∀ a, 0 < x a ∧ profileGridEndpoint n (x a) ≤ α then
    G (fun a => profileGridEndpoint n (x a)) *
      ∏ a, rateKernel (t (profileGridEndpoint n (x (τ a)))) (f (x a))
  else 0
```

### cyclicLimitKernel

def; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:65)

```lean
def cyclicLimitKernel {r : ℕ} (α : ℝ) (τ : Equiv.Perm (Fin r))
    (G : (Fin r → ℝ) → ℝ) (t f : ℝ → ℝ) : (Fin r → ℝ) → ℝ :=
  (cyclicBulkInterior r α).indicator (fun x =>
    G x * ∏ a, rateKernel (t (x (τ a))) (f (x a)))
```

### abs_prod_sub_prod_le_envelope

lemma; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:72)

A quantitative finite-product telescoping bound. The base factors need
only the bounds H; each replacement is charged its own error E.

```lean
lemma abs_prod_sub_prod_le_envelope {ι : Type*} (s : Finset ι)
    (A B H E : ι → ℝ) (hH : ∀ i ∈ s, 0 ≤ H i) (hE : ∀ i ∈ s, 0 ≤ E i)
    (hB : ∀ i ∈ s, |B i| ≤ H i) (hAB : ∀ i ∈ s, |A i - B i| ≤ E i) :
    |(∏ i ∈ s, A i) - ∏ i ∈ s, B i| ≤
      (∏ i ∈ s, (H i + E i)) - ∏ i ∈ s, H i
```

### cyclic_ae_coordinates

lemma; [source line 117](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:117)

Product-space almost-everywhere statements are lifted coordinatewise.

```lean
lemma cyclic_ae_coordinates {r : ℕ} {p : ℝ → Prop}
    (hp : ∀ᵐ y ∂profileMeasure, p y) :
    ∀ᵐ x ∂cyclicProfileMeasure r, ∀ a, p (x a)
```

### integrable_cyclic_source_product

lemma; [source line 122](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:122)

```lean
lemma integrable_cyclic_source_product {r : ℕ} {f : ℝ → ℝ}
    (hf : Integrable f profileMeasure) :
    Integrable (fun x : Fin r → ℝ => ∏ a, f (x a)) (cyclicProfileMeasure r)
```

### integral_cyclic_source_product

lemma; [source line 127](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:127)

```lean
lemma integral_cyclic_source_product {r : ℕ} (f : ℝ → ℝ) :
    (∫ x : Fin r → ℝ, ∏ a, f (x a) ∂cyclicProfileMeasure r) =
      (∫ y, f y ∂profileMeasure) ^ r
```

### exists_cyclic_test_extension

theorem; [source line 136](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:136)

A continuous function on the source cube admits an ambient function
continuous on that cube. No ambient continuity is asserted or needed; this
also covers empty cubes and degenerate endpoint cubes.

```lean
theorem exists_cyclic_test_extension {r : ℕ} {α : ℝ}
    (g : cyclicBulkCube r α → ℝ) (hg : Continuous g) :
    ∃ G : (Fin r → ℝ) → ℝ, ContinuousOn G (cyclicBulkCube r α) ∧
      ∀ x : cyclicBulkCube r α, G x.val = g x
```

### measurable_cyclic_grid_comp

lemma; [source line 149](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:149)

```lean
lemma measurable_cyclic_grid_comp {r : ℕ} (n : ℕ) (G : (Fin r → ℝ) → ℝ) :
    Measurable (fun x : Fin r → ℝ => G (fun a => profileGridEndpoint n (x a)))
```

### aestronglyMeasurable_cyclicGridKernel

lemma; [source line 159](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:159)

```lean
lemma aestronglyMeasurable_cyclicGridKernel {r : ℕ} (n : ℕ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f profileMeasure) :
    AEStronglyMeasurable (cyclicGridKernel n α τ G t f) (cyclicProfileMeasure r)
```

### abs_cyclicGridKernel_le

lemma; [source line 188](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:188)

```lean
lemma abs_cyclicGridKernel_le {r n : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t f : ℝ → ℝ)
    (hB : 0 ≤ B) (hG : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    {x : Fin r → ℝ} (hf : ∀ a, 0 ≤ f (x a)) :
    |cyclicGridKernel n α τ G t f x| ≤ B * ∏ a, f (x a)
```

### integrable_cyclicGridKernel

lemma; [source line 207](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:207)

```lean
lemma integrable_cyclicGridKernel {r n : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ)
    (hB : 0 ≤ B) (hG : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    {f : ℝ → ℝ} (hf : Integrable f profileMeasure)
    (hf0 : ∀ᵐ y ∂profileMeasure, 0 ≤ f y) :
    Integrable (cyclicGridKernel n α τ G t f) (cyclicProfileMeasure r)
```

### abs_cyclicGridKernel_sub_le

lemma; [source line 219](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:219)

```lean
lemma abs_cyclicGridKernel_sub_le {r n : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t f h : ℝ → ℝ)
    (hB : 0 ≤ B) (hG : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    {x : Fin r → ℝ} (hf : ∀ a, 0 ≤ f (x a)) (hh : ∀ a, 0 ≤ h (x a)) :
    |cyclicGridKernel n α τ G t h x - cyclicGridKernel n α τ G t f x| ≤
      B * ((∏ a, (f (x a) + |h (x a) - f (x a)|)) - ∏ a, f (x a))
```

### integral_cyclicGridKernel_sub_le

theorem; [source line 248](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:248)

Exact integrated L1 product error; finiteness of both products and of
the error envelope is established before subtracting their integrals.

```lean
theorem integral_cyclicGridKernel_sub_le {r n : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ)
    (hB : 0 ≤ B) (hG : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    {f h : ℝ → ℝ} (hf : Integrable f profileMeasure) (hh : Integrable h profileMeasure)
    (hf0 : ∀ᵐ y ∂profileMeasure, 0 ≤ f y) (hh0 : ∀ᵐ y ∂profileMeasure, 0 ≤ h y) :
    |(∫ x, cyclicGridKernel n α τ G t h x ∂cyclicProfileMeasure r) -
        ∫ x, cyclicGridKernel n α τ G t f x ∂cyclicProfileMeasure r| ≤
      B * (((∫ y, f y ∂profileMeasure) +
        ∫ y, |h y - f y| ∂profileMeasure) ^ r - (∫ y, f y ∂profileMeasure) ^ r)
```

### ProfileLimit.tendsto_cyclic_grid_profile_replacement

theorem; [source line 285](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:285)

The source's L1 hypothesis alone gives the product replacement, uniformly
over the cellwise rank times. No boundedness of f or pointwise convergence
of the step profiles is assumed.

```lean
theorem ProfileLimit.tendsto_cyclic_grid_profile_replacement {w : WeightArray}
    {f : ℝ → ℝ} (hf : ProfileLimit w f) {r : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ)
    (hB : 0 ≤ B) (hG : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) :
    Tendsto (fun n =>
      (∫ x, cyclicGridKernel n α τ G t (stepProfile w (n + 1)) x ∂cyclicProfileMeasure r) -
        ∫ x, cyclicGridKernel n α τ G t f x ∂cyclicProfileMeasure r) atTop (𝓝 0)
```

### tendsto_cyclicGridKernel

lemma; [source line 302](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:302)

```lean
lemma tendsto_cyclicGridKernel {r : ℕ} {α : ℝ} (τ : Equiv.Perm (Fin r))
    {G : (Fin r → ℝ) → ℝ} {t f : ℝ → ℝ}
    (hG : ContinuousOn G (cyclicBulkCube r α))
    (ht : ContinuousOn t (Icc (0 : ℝ) α)) {x : Fin r → ℝ}
    (hx0 : ∀ a, 0 < x a) (hxa : ∀ a, x a ≠ α) :
    Tendsto (fun n => cyclicGridKernel n α τ G t f x) atTop
      (𝓝 (cyclicLimitKernel α τ G t f x))
```

### ae_tendsto_cyclicGridKernel

lemma; [source line 346](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:346)

```lean
lemma ae_tendsto_cyclicGridKernel {r : ℕ} {α : ℝ} (τ : Equiv.Perm (Fin r))
    {G : (Fin r → ℝ) → ℝ} {t f : ℝ → ℝ}
    (hG : ContinuousOn G (cyclicBulkCube r α))
    (ht : ContinuousOn t (Icc (0 : ℝ) α)) :
    ∀ᵐ x ∂cyclicProfileMeasure r,
      Tendsto (fun n => cyclicGridKernel n α τ G t f x) atTop
        (𝓝 (cyclicLimitKernel α τ G t f x))
```

### integrable_cyclicLimitKernel

lemma; [source line 360](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:360)

```lean
lemma integrable_cyclicLimitKernel {r : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) {G : (Fin r → ℝ) → ℝ} {t f : ℝ → ℝ}
    (hB : 0 ≤ B) (hG : ContinuousOn G (cyclicBulkCube r α))
    (hGB : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht0 : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    (hf : Integrable f profileMeasure) (hf0 : ∀ᵐ y ∂profileMeasure, 0 ≤ f y) :
    Integrable (cyclicLimitKernel α τ G t f) (cyclicProfileMeasure r)
```

### tendsto_integral_cyclicGridKernel

theorem; [source line 378](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:378)

Dominated convergence performs the cell-endpoint passage for the fixed
limiting profile, using the integrable product of its source rates.

```lean
theorem tendsto_integral_cyclicGridKernel {r : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) {G : (Fin r → ℝ) → ℝ} {t f : ℝ → ℝ}
    (hB : 0 ≤ B) (hG : ContinuousOn G (cyclicBulkCube r α))
    (hGB : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht0 : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    (hf : Integrable f profileMeasure) (hf0 : ∀ᵐ y ∂profileMeasure, 0 ≤ f y) :
    Tendsto (fun n => ∫ x, cyclicGridKernel n α τ G t f x ∂cyclicProfileMeasure r)
      atTop (𝓝 (∫ x, cyclicLimitKernel α τ G t f x ∂cyclicProfileMeasure r))
```

### ProfileLimit.tendsto_integral_cyclic_stepKernel

theorem; [source line 397](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:397)

The complete analytic step-profile integral passage, with a signed
coefficient continuous only on the source cube.

```lean
theorem ProfileLimit.tendsto_integral_cyclic_stepKernel {w : WeightArray}
    {f : ℝ → ℝ} (hf : ProfileLimit w f) {r : ℕ} {α : ℝ}
    (τ : Equiv.Perm (Fin r)) {G : (Fin r → ℝ) → ℝ} {t : ℝ → ℝ}
    (hG : ContinuousOn G (cyclicBulkCube r α))
    (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht0 : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) :
    Tendsto (fun n => ∫ x, cyclicGridKernel n α τ G t (stepProfile w (n + 1)) x
      ∂cyclicProfileMeasure r) atTop
      (𝓝 (∫ x, cyclicLimitKernel α τ G t f x ∂cyclicProfileMeasure r))
```

### cyclicDensityCoefficient

def; [source line 419](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:419)

Incorporate the target-rank denominators in the signed continuous
coefficient; each source coordinate occurs exactly once in the numerator.

```lean
def cyclicDensityCoefficient {r : ℕ} (f : ℝ → ℝ) (τ : Equiv.Perm (Fin r))
    (g : (Fin r → ℝ) → ℝ) (x : Fin r → ℝ) : ℝ :=
  g x * ∏ a, (profileD profileMeasure f (profileQuantile profileMeasure f (x (τ a))))⁻¹
```

### continuousOn_cyclicDensityCoefficient

lemma; [source line 423](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:423)

```lean
lemma continuousOn_cyclicDensityCoefficient {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {r : ℕ} {α : ℝ} (hα : α < 1)
    (τ : Equiv.Perm (Fin r)) {g : (Fin r → ℝ) → ℝ}
    (hg : ContinuousOn g (cyclicBulkCube r α)) :
    ContinuousOn (cyclicDensityCoefficient f τ g) (cyclicBulkCube r α)
```

### cyclicLimitKernel_density_eq

lemma; [source line 437](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:437)

```lean
lemma cyclicLimitKernel_density_eq {r : ℕ} (f : ℝ → ℝ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicLimitKernel α τ (cyclicDensityCoefficient f τ g)
      (profileQuantile profileMeasure f) f =
      (cyclicBulkInterior r α).indicator
        (fun x => g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a)))
```

### cyclicProfileMeasure_restrict_bulk

lemma; [source line 450](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:450)

```lean
lemma cyclicProfileMeasure_restrict_bulk {r : ℕ} {α : ℝ} (hα : α < 1) :
    (cyclicProfileMeasure r).restrict (cyclicBulkInterior r α) =
      volume.restrict (cyclicBulkInterior r α)
```

### cyclicProfileIntegral_eq_volume

theorem; [source line 465](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:465)

The product profile measure and half-open cube recover exactly the
paper's Lebesgue integral on the closed cube, including its endpoints.

```lean
theorem cyclicProfileIntegral_eq_volume {r : ℕ} (f : ℝ → ℝ) {α : ℝ} (hα : α < 1)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicProfileIntegral f α τ g =
      ∫ x in cyclicBulkCube r α, g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a))
```

### cyclicRaceSum_of_nonpos

theorem; [source line 474](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:474)

```lean
theorem cyclicRaceSum_of_nonpos {n r : ℕ} (w : Weights n) {α : ℝ}
    (hα : α ≤ 0) (hr : 0 < r) (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicRaceSum w α τ g = 0
```

### cyclicProfileIntegral_of_nonpos

theorem; [source line 487](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:487)

```lean
theorem cyclicProfileIntegral_of_nonpos {r : ℕ} (f : ℝ → ℝ) {α : ℝ}
    (hα : α ≤ 0) (hr : 0 < r) (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicProfileIntegral f α τ g = 0
```

### cyclicProfileCell

def; [source line 497](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:497)

```lean
def cyclicProfileCell {r : ℕ} (n : ℕ) (i : Fin r → Fin (n + 1)) : Set (Fin r → ℝ) :=
  Set.pi Set.univ (fun a => Ioc ((i a).val / (n + 1 : ℕ) : ℝ)
    (((i a).val + 1 : ℝ) / (n + 1 : ℕ)))
```

### measurableSet_cyclicProfileCell

lemma; [source line 501](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:501)

```lean
lemma measurableSet_cyclicProfileCell {r : ℕ} (n : ℕ) (i : Fin r → Fin (n + 1)) :
    MeasurableSet (cyclicProfileCell n i)
```

### cyclicProfileCell_real_measure

lemma; [source line 505](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:505)

```lean
lemma cyclicProfileCell_real_measure {r : ℕ} (n : ℕ) (i : Fin r → Fin (n + 1)) :
    (cyclicProfileMeasure r).real (cyclicProfileCell n i) = 1 / (n + 1 : ℕ) ^ r
```

### cyclicProfileCell_unique

lemma; [source line 514](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:514)

```lean
lemma cyclicProfileCell_unique {r : ℕ} {n : ℕ} {x : Fin r → ℝ}
    {i j : Fin r → Fin (n + 1)} (hi : x ∈ cyclicProfileCell n i)
    (hj : x ∈ cyclicProfileCell n j) : i = j
```

### cyclicKernelGridSum

def; [source line 525](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:525)

```lean
def cyclicKernelGridSum {n r : ℕ} (w : Weights n) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ) : ℝ := by
  classical
  exact (∑ i : Fin r → Fin n,
    if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
      G (fun a => ((i a).val + 1 : ℝ) / n) *
        ∏ a, rateKernel (t (((i (τ a)).val + 1 : ℝ) / n)) (w.rate (i a))
    else 0) / (n : ℝ) ^ r
```

### integral_cyclicGridKernel_step

theorem; [source line 536](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:536)

The exact multivariate cell identity: every box has mass n^(-r), and
the terminal fractional box is included precisely by its right endpoint.

```lean
theorem integral_cyclicGridKernel_step (w : WeightArray) {r : ℕ} (n : ℕ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ) :
    (∫ x, cyclicGridKernel n α τ G t (stepProfile w (n + 1)) x ∂cyclicProfileMeasure r) =
      cyclicKernelGridSum (w (n + 1)) α τ G t
```

### finiteCyclicDensity

def; [source line 575](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:575)

The finite-row numerator uses its actual source rate, never a sampled
value of the limiting profile. This is the kernel in source 1040–1045.

```lean
def finiteCyclicDensity {n : ℕ} (w : Weights n) (f : ℝ → ℝ) (i j : Fin n) : ℝ :=
  rateKernel (profileQuantile profileMeasure f (((j.val : ℝ) + 1) / n)) (w.rate i) /
    profileD profileMeasure f (profileQuantile profileMeasure f (((j.val : ℝ) + 1) / n))
```

### cyclicDeterministicSum

def; [source line 579](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:579)

```lean
def cyclicDeterministicSum {n r : ℕ} (w : Weights n) (f : ℝ → ℝ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) : ℝ := by
  classical
  exact (∑ i : Fin r → Fin n,
    if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
      g (fun a => ((i a).val + 1 : ℝ) / n) * ∏ a, finiteCyclicDensity w f (i a) (i (τ a))
    else 0) / (n : ℝ) ^ r
```

### cyclicDeterministicSum_eq_kernelGridSum

lemma; [source line 587](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:587)

```lean
lemma cyclicDeterministicSum_eq_kernelGridSum {n r : ℕ} (w : Weights n)
    (f : ℝ → ℝ) (α : ℝ) (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicDeterministicSum w f α τ g =
      cyclicKernelGridSum w α τ (cyclicDensityCoefficient f τ g) (profileQuantile profileMeasure f)
```

### ProfileLimit.cyclic_deterministic_limit

theorem; [source line 605](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:605)

The complete deterministic cyclic kernel limit in source 1065–1075.
The tuple sum here includes repeated coordinates; the subsequent finite-sum
reduction controls their removal along with nearby coordinates.

```lean
theorem ProfileLimit.cyclic_deterministic_limit {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {r : ℕ} {α : ℝ} (hα : α < 1)
    (τ : Equiv.Perm (Fin r)) {g : (Fin r → ℝ) → ℝ}
    (hg : ContinuousOn g (cyclicBulkCube r α)) :
    Tendsto (fun n => cyclicDeterministicSum (w (n + 1)) f α τ g) atTop
      (𝓝 (cyclicProfileIntegral f α τ g))
```

### ProfileLimit.integrable_cyclic_density

theorem; [source line 626](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicAnalytic.lean:626)

The limiting cyclic integral is finite under the original profile
hypothesis and signed test-function assumption.

```lean
theorem ProfileLimit.integrable_cyclic_density {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {r : ℕ} {α : ℝ} (hα : α < 1)
    (τ : Equiv.Perm (Fin r)) {g : (Fin r → ℝ) → ℝ}
    (hg : ContinuousOn g (cyclicBulkCube r α)) :
    IntegrableOn (fun x => g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a)))
      (cyclicBulkCube r α)
```


## Luce/Section5CyclicReduction.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology BigOperators
namespace Luce
```

### prod_one_exception

lemma; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:19)

```lean
lemma prod_one_exception {r : ℕ} (a : Fin r) (H T : ℝ) :
    (∏ b : Fin r, if b = a then H else T) = H * T ^ (r - 1)
```

### sum_tuple_high_rate_le

theorem; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:34)

The exact source mass in the high-rate union bound, with the coordinate
union counted at most r times and every other coordinate summed freely.

```lean
theorem sum_tuple_high_rate_le {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → Prop) [DecidablePred p] :
    (∑ i : Fin r → ι, if ∃ a, p (i a) then ∏ a, w (i a) else 0) ≤
      (r : ℝ) * (∑ k, if p k then w k else 0) * (∑ k, w k) ^ (r - 1)
```

### cyclicCellStep

def; [source line 83](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:83)

Piecewise constant values on the actual multivariate profile cells.

```lean
def cyclicCellStep {r : ℕ} (n : ℕ) (b : (Fin r → Fin (n + 1)) → ℝ)
    (x : Fin r → ℝ) : ℝ :=
  ∑ i, (cyclicProfileCell n i).indicator (fun _ => b i) x
```

### cyclicCellStep_eq_of_mem

lemma; [source line 87](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:87)

```lean
lemma cyclicCellStep_eq_of_mem {r n : ℕ} (b : (Fin r → Fin (n + 1)) → ℝ)
    {x : Fin r → ℝ} {i : Fin r → Fin (n + 1)} (hi : x ∈ cyclicProfileCell n i) :
    cyclicCellStep n b x = b i
```

### integrable_cyclicCellStep

lemma; [source line 96](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:96)

```lean
lemma integrable_cyclicCellStep {r : ℕ} (n : ℕ) (b : (Fin r → Fin (n + 1)) → ℝ) :
    Integrable (cyclicCellStep n b) (cyclicProfileMeasure r)
```

### integral_cyclicCellStep

lemma; [source line 101](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:101)

```lean
lemma integral_cyclicCellStep {r : ℕ} (n : ℕ) (b : (Fin r → Fin (n + 1)) → ℝ) :
    (∫ x, cyclicCellStep n b x ∂cyclicProfileMeasure r) =
      (∑ i, b i) / (n + 1 : ℕ) ^ r
```

### cyclicProfileMeasure_injective_ae

lemma; [source line 113](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:113)

```lean
lemma cyclicProfileMeasure_injective_ae (r : ℕ) :
    ∀ᵐ x ∂cyclicProfileMeasure r, Function.Injective x
```

### eventually_cyclic_grid_separated

lemma; [source line 140](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:140)

Every fixed distinct coordinate vector has eventually separated cell
endpoints. Thus the only vectors omitted by separated-rank asymptotics form
the proved null union of geometric diagonals.

```lean
lemma eventually_cyclic_grid_separated {r : ℕ} (hr : 0 < r) {x : Fin r → ℝ}
    (hx0 : ∀ a, 0 ≤ x a) (hinj : Function.Injective x) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ᶠ n in atTop, ∀ a b : Fin r, a ≠ b →
      ζ ≤ |profileGridEndpoint n (x a) - profileGridEndpoint n (x b)|
```

### tendsto_cyclic_array_sum_of_separated

theorem; [source line 169](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:169)

A uniformly bounded array whose separated-grid values tend uniformly to
zero has normalized sum tending to zero. The near-diagonal contribution is
removed by dominated convergence on the actual grid cells.

```lean
theorem tendsto_cyclic_array_sum_of_separated {r : ℕ} (hr : 0 < r)
    (A : (n : ℕ) → (Fin r → Fin (n + 1)) → ℝ) {B : ℝ}
    (hbound : ∀ᶠ n in atTop, ∀ i, |A n i| ≤ B)
    (hsep : ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i : Fin r → Fin (n + 1),
        (∀ a b : Fin r, a ≠ b →
          ζ ≤ |((i a).val + 1 : ℝ) / (n + 1 : ℕ) - ((i b).val + 1 : ℝ) / (n + 1 : ℕ)|) →
        |A n i| < ε) :
    Tendsto (fun n => (∑ i, A n i) / (n + 1 : ℕ) ^ r) atTop (𝓝 0)
```

### ProfileLimit.eventually_rowMean_le

lemma; [source line 209](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:209)

```lean
lemma ProfileLimit.eventually_rowMean_le {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ) ≤ C
```

### normalized_tuple_high_rate_le

lemma; [source line 230](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:230)

Normalized high-rate product mass, exactly the expression in (1055–1058).
The source's distinctness and bulk restrictions may be dropped because every
summand on the right is nonnegative.

```lean
lemma normalized_tuple_high_rate_le {r : ℕ} (hr : 0 < r) (w : WeightArray)
    (n : ℕ) (M : ℝ) :
    (∑ i : Fin r → Fin (n + 1),
      if ∃ a, M < (w (n + 1)).rate (i a) then ∏ a, (w (n + 1)).rate (i a) else 0) /
        (n + 1 : ℕ) ^ r ≤
      (r : ℝ) * highRateMass w (n + 1) M *
        ((∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ)) ^ (r - 1)
```

### cyclic_array_truncation_error

lemma; [source line 253](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:253)

```lean
lemma cyclic_array_truncation_error {r : ℕ} (hr : 0 < r) (w : WeightArray)
    (n : ℕ) (M : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (A : (Fin r → Fin (n + 1)) → ℝ)
    (hA : ∀ i, |A i| ≤ K * ∏ a, (w (n + 1)).rate (i a)) :
    |(∑ i, A i) / (n + 1 : ℕ) ^ r -
      (∑ i, if ∀ a, (w (n + 1)).rate (i a) ≤ M then A i else 0) / (n + 1 : ℕ) ^ r| ≤
      K * ((r : ℝ) * highRateMass w (n + 1) M *
        ((∑ i : Fin (n + 1), (w (n + 1)).rate i) / (n + 1 : ℕ)) ^ (r - 1))
```

### ProfileLimit.tendsto_weighted_cyclic_array_sum

theorem; [source line 287](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:287)

The complete truncation-and-summation step. Its hypotheses are precisely
a weighted product bound and bounded-rate separated-grid convergence; the
actual microscopic probability estimate will discharge the latter. This is
an auxiliary reduction, not a claimed proof of Lemma 5.2 by assumption.

```lean
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
    Tendsto (fun n => (∑ i, A n i) / (n + 1 : ℕ) ^ r) atTop (𝓝 0)
```

### cyclicTupleProbability

def; [source line 363](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:363)

```lean
def cyclicTupleProbability {n r : ℕ} (w : Weights n) (τ : Equiv.Perm (Fin r))
    (i : Fin r → Fin n) : ℝ :=
  (exponentialRace w).real {E | ∀ a, raceRank E (i a) = (i (τ a)).val + 1}
```

### cyclicScaledRaceTerm

def; [source line 367](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:367)

```lean
def cyclicScaledRaceTerm {n r : ℕ} (w : Weights n) (τ : Equiv.Perm (Fin r))
    (i : Fin r → Fin n) : ℝ := by
  classical
  exact if Function.Injective i then (n : ℝ) ^ r * cyclicTupleProbability w τ i else 0
```

### cyclicComparisonArray

def; [source line 375](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:375)

Exact signed error between the scaled rank probability and its finite
rate kernel, extended by zero outside the bulk. Repeated tuples contribute
zero probability, while their kernel contribution is explicitly retained.

```lean
def cyclicComparisonArray {n r : ℕ} (w : Weights n) (f : ℝ → ℝ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) (i : Fin r → Fin n) : ℝ := by
  classical
  exact if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
    g (fun a => ((i a).val + 1 : ℝ) / n) *
      (cyclicScaledRaceTerm w τ i - ∏ a, finiteCyclicDensity w f (i a) (i (τ a)))
  else 0
```

### sum_embedding_eq_sum_injective

lemma; [source line 383](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:383)

```lean
lemma sum_embedding_eq_sum_injective {n r : ℕ} (b : (Fin r → Fin n) → ℝ) :
    (∑ i : Fin r ↪ Fin n, b i) =
      ∑ i : Fin r → Fin n, if Function.Injective i then b i else 0
```

### cyclicRaceSum_eq_function_sum

lemma; [source line 398](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:398)

```lean
lemma cyclicRaceSum_eq_function_sum {n r : ℕ} (w : Weights n) (hn : 0 < n)
    (α : ℝ) (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicRaceSum w α τ g =
      ∑ i : Fin r → Fin n, if Function.Injective i then
        (if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
          g (fun a => ((i a).val + 1 : ℝ) / n) * cyclicTupleProbability w τ i else 0)
      else 0
```

### normalized_cyclicComparisonArray

lemma; [source line 414](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:414)

Exact passage between the injective tuple sum in the paper and the full
cell-array error, including all repeated-index kernel terms.

```lean
lemma normalized_cyclicComparisonArray {n r : ℕ} (w : Weights n) (hn : 0 < n)
    (f : ℝ → ℝ) (α : ℝ) (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    (∑ i : Fin r → Fin n, cyclicComparisonArray w f α τ g i) / (n : ℝ) ^ r =
      cyclicRaceSum w α τ g - cyclicDeterministicSum w f α τ g
```

### finiteCyclicDensity_bounds

lemma; [source line 434](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:434)

```lean
lemma finiteCyclicDensity_bounds {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {n : ℕ} (i j : Fin n)
    (hj : ((j.val : ℝ) + 1) / n ≤ α) :
    0 ≤ finiteCyclicDensity (w n) f i j ∧
      finiteCyclicDensity (w n) f i j ≤ (w n).rate i /
        profileD profileMeasure f (profileQuantile profileMeasure f α)
```

### ProfileLimit.cyclicComparisonArray_weighted_bound

theorem; [source line 450](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:450)

Both the actual probability and the finite kernel are dominated by the
same product of source rates. No rate truncation is used in this bound.

```lean
theorem ProfileLimit.cyclicComparisonArray_weighted_bound {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {r : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (τ : Equiv.Perm (Fin r)) {g : (Fin r → ℝ) → ℝ}
    (hg : ContinuousOn g (cyclicBulkCube r α)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ i : Fin r → Fin (n + 1),
      |cyclicComparisonArray (w (n + 1)) f α τ g i| ≤
        K * ∏ a, (w (n + 1)).rate (i a)
```

### ProfileLimit.cyclic_local_of_bounded_marked_asymptotic

theorem; [source line 526](D:/princeton/Research/Lean/Lean_luce/Luce/Section5CyclicReduction.lean:526)

The complete finite-sum reduction of Lemma 5.2 to its bounded marked
asymptotic (1040–1045). The microscopic premise is explicit and must be
proved from the actual race; this declaration is not advertised as the
completed probabilistic lemma. Every other truncation, diagonal, profile,
integrability and signed-test-function step is discharged here.

```lean
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
      (𝓝 (cyclicProfileIntegral f α τ g))
```


## Luce/Section5DeletedGaps.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce
```

### deletedClockLabel

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:20)

```lean
def deletedClockLabel {n : ℕ} (removed : Finset (Fin n))
    (k : Fin (Finset.univ \ removed).card) : Fin n :=
  ((Finset.univ \ removed).equivFin.symm k).val
```

### deletedClockLabel_injective

lemma; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:24)

```lean
lemma deletedClockLabel_injective {n : ℕ} (removed : Finset (Fin n)) :
    Injective (deletedClockLabel removed)
```

### compactDeletedClocks

def; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:30)

```lean
def compactDeletedClocks {n : ℕ} (removed : Finset (Fin n)) (old : Fin n → ℝ) :
    Fin (Finset.univ \ removed).card → ℝ := fun k => old (deletedClockLabel removed k)
```

### compactDeletedWeights

def; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:33)

```lean
def compactDeletedWeights {n : ℕ} (w : Weights n) (removed : Finset (Fin n)) :
    Weights (Finset.univ \ removed).card :=
  ⟨fun k => w.rate (deletedClockLabel removed k), fun k => w.positive _⟩
```

### compactDeletedClocks_measurable

lemma; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:37)

```lean
lemma compactDeletedClocks_measurable {n : ℕ} (removed : Finset (Fin n)) :
    Measurable (compactDeletedClocks removed)
```

### compactDeletedClocks_measurePreserving

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:43)

Exact equality of the actual unmarked clock law with the compacted
exponential race. No independence hypothesis is added.

```lean
theorem compactDeletedClocks_measurePreserving {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) :
    MeasurePreserving (compactDeletedClocks removed) (exponentialRace w)
      (exponentialRace (compactDeletedWeights w removed))
```

### compactDeletedClocks_injective

lemma; [source line 58](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:58)

```lean
lemma compactDeletedClocks_injective {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (hold : Injective old) : Injective (compactDeletedClocks removed old)
```

### compactDeletedClocks_card

lemma; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:62)

```lean
lemma compactDeletedClocks_card {n : ℕ} (removed : Finset (Fin n)) :
    (Finset.univ \ removed).card = n - removed.card
```

### compactMarkedClocks_card

lemma; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:66)

```lean
lemma compactMarkedClocks_card {n r : ℕ} (u : Fin r → Fin n) (hu : Injective u) :
    (Finset.univ \ Finset.univ.image u).card = n - r
```

### clockBeforeCount_compactDeletedClocks

theorem; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:73)

Relabeling the remaining coordinates neither changes a before-count
nor introduces multiplicities.

```lean
theorem clockBeforeCount_compactDeletedClocks {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (t : ℝ) :
    clockBeforeCount (compactDeletedClocks removed old) t = deletedBeforeCount removed old t
```

### consecutiveGapLower

def; [source line 83](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:83)

The finite gap's lower endpoint, with `T₀=0`; `q=0` is the first gap.

```lean
def consecutiveGapLower {m : ℕ} (times : Fin m → ℝ) (htimes : Injective times)
    (q : Fin m) : ℝ :=
  if h : q.val = 0 then 0 else arrivalTime times htimes ⟨q.val - 1, by omega⟩
```

### consecutiveGapLower_nonneg

lemma; [source line 87](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:87)

```lean
lemma consecutiveGapLower_nonneg {m : ℕ} (times : Fin m → ℝ) (htimes : Injective times)
    (hpos : ∀ i, 0 ≤ times i) (q : Fin m) : 0 ≤ consecutiveGapLower times htimes q
```

### mem_consecutiveGap_iff_count

theorem; [source line 96](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:96)

Exact order-statistic description of each nonterminal count gap.
The only excluded times are the finitely many old clock values.

```lean
theorem mem_consecutiveGap_iff_count {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (hpos : ∀ i, 0 ≤ times i) (q : Fin m) (t : ℝ)
    (havoid : ∀ i, t ≠ times i) :
    t ∈ Ioo (consecutiveGapLower times htimes q) (arrivalTime times htimes q) ↔
      0 < t ∧ clockBeforeCount times t = q.val
```

### deletedGapKernel_eq_interval_measure

theorem; [source line 119](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedGaps.lean:119)

Exact correspondence with the source's unmarked open gap, including
the initial lower endpoint.

```lean
theorem deletedGapKernel_eq_interval_measure {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hold : Injective old)
    (hpos : ∀ i, 0 ≤ old i) (i : Fin n) (q : Fin (Finset.univ \ removed).card) :
    deletedGapKernel w removed old i q.val = expMeasure (w.rate i)
      (Ioo (consecutiveGapLower (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold) q)
        (arrivalTime (compactDeletedClocks removed old)
          (compactDeletedClocks_injective removed old hold) q))
```


## Luce/Section5DeletedRace.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### deletedEmpiricalArrival

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:21)

The unmarked empirical arrival count, normalized by the original row
size `n`, as in the deleted-chain proof in Section 5.

```lean
def deletedEmpiricalArrival {n : ℕ} (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ removed, arrivalAt t (clocks i)) / n
```

### deletedEmpiricalRemainingGe

def; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:26)

The unmarked weak-survival rate, again divided by the original `n`.

```lean
def deletedEmpiricalRemainingGe {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ removed, if t ≤ clocks i then w.rate i else 0) / n
```

### deletedEmpiricalArrival_nonneg

lemma; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:30)

```lean
lemma deletedEmpiricalArrival_nonneg {n : ℕ} (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) : 0 ≤ deletedEmpiricalArrival removed clocks t
```

### deletedEmpiricalArrival_monotone

lemma; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:35)

```lean
lemma deletedEmpiricalArrival_monotone {n : ℕ} (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) : Monotone (deletedEmpiricalArrival removed clocks)
```

### empiricalArrival_sub_deleted

lemma; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:42)

Exact finite-sum accounting, before any probabilistic estimate.

```lean
lemma empiricalArrival_sub_deleted {n : ℕ} (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) :
    empiricalArrival clocks t - deletedEmpiricalArrival removed clocks t =
      (∑ i ∈ removed, arrivalAt t (clocks i)) / n
```

### deletedEmpiricalArrival_error

lemma; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:54)

Deleting `r` clocks changes the empirical arrival count by at most `r/n`,
uniformly over times, clock configurations, and the removed labels.

```lean
lemma deletedEmpiricalArrival_error {n r : ℕ} (removed : Finset (Fin n))
    (hr : removed.card ≤ r) (clocks : Fin n → ℝ) (t : ℝ) :
    |deletedEmpiricalArrival removed clocks t - empiricalArrival clocks t| ≤ (r : ℝ) / n
```

### empiricalRemainingGe_sub_deleted

lemma; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:68)

Exact finite-sum accounting for the unmarked remaining rate.

```lean
lemma empiricalRemainingGe_sub_deleted {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (clocks : Fin n → ℝ) (t : ℝ) :
    empiricalRemainingGe w clocks t - deletedEmpiricalRemainingGe w removed clocks t =
      (∑ i ∈ removed, if t ≤ clocks i then w.rate i else 0) / n
```

### deletedEmpiricalRemainingGe_error

lemma; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:80)

The source's uniform deletion error. Bounded marked rates are unnecessary:
the largest normalized weight is already negligible under Assumption 1.1.

```lean
lemma deletedEmpiricalRemainingGe_error (w : WeightArray) {n r : ℕ}
    (removed : Finset (Fin (n + 1))) (hr : removed.card ≤ r)
    (clocks : Fin (n + 1) → ℝ) (t : ℝ) :
    |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t -
      empiricalRemainingGe (w (n + 1)) clocks t| ≤
        (r : ℝ) * (rowMaxRate w n / (n + 1 : ℕ))
```

### section5_uniform_deleted_arrival

theorem; [source line 112](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:112)

The deleted empirical CDF converges uniformly on compact time intervals,
simultaneously over all sets of at most `r` deleted clocks (source 1035–1038).

```lean
theorem section5_uniform_deleted_arrival
    (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f) (r : ℕ) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t ∈ Icc 0 T, ε ≤ |deletedEmpiricalArrival removed clocks t -
          profileF profileMeasure f t|}) atTop (𝓝 0)
```

### section5_uniform_deleted_remaining

theorem; [source line 145](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:145)

The corresponding deleted remaining-rate convergence, with normalization
exposed exactly as in the source's full race estimate.

```lean
theorem section5_uniform_deleted_remaining
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t ∈ Icc 0 T, ε ≤ |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t -
          profileD profileMeasure f t|}) atTop (𝓝 0)
```

### deletedEmpiricalArrival_eq_count

lemma; [source line 178](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:178)

The empirical coordinate is the exact number of arrived unmarked
clocks divided by `n`, retaining both the global normalization and labels.

```lean
lemma deletedEmpiricalArrival_eq_count {n : ℕ} (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) :
    deletedEmpiricalArrival removed clocks t =
      (((Finset.univ \ removed).filter (fun i => clocks i ≤ t)).card : ℝ) / n
```

### section5_uniform_deleted_quantile

theorem; [source line 189](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:189)

Uniform inverse-time control for the actual deleted process. Evaluating
this at its successive arrival times gives the unmarked order-statistic
estimate used at source 1035–1038. The theorem is stronger: it controls every
nonnegative time whose unmarked empirical rank lies in the bulk, including
the entire intervening gaps.

```lean
theorem section5_uniform_deleted_quantile
    (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f) (r : ℕ)
    {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |t - profileQuantile profileMeasure f
            (deletedEmpiricalArrival removed clocks t)|}) atTop (𝓝 0)
```

### section5_uniform_deleted_denominator

theorem; [source line 244](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:244)

The unmarked remaining rate at every bulk time has the deterministic
value at its unmarked quantile, uniformly over all permitted deletions.
This proves the random-time substitution needed before studying gap moments.

```lean
theorem section5_uniform_deleted_denominator
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n + 1))
      {clocks | ∃ removed : Finset (Fin (n + 1)), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t -
            profileD profileMeasure f (profileQuantile profileMeasure f
              (deletedEmpiricalArrival removed clocks t))|}) atTop (𝓝 0)
```

### section5_deleted_order_statistics

theorem; [source line 332](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:332)

Original-row version of both deleted-chain order-statistic conclusions.
The exact count formula above identifies the spatial coordinate at each
unmarked arrival as `q/n`; the omitted empty initial row is restored here.

```lean
theorem section5_deleted_order_statistics
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ removed : Finset (Fin n), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |t - profileQuantile profileMeasure f
            (deletedEmpiricalArrival removed clocks t)|}) atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ removed : Finset (Fin n), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |deletedEmpiricalRemainingGe (w n) removed clocks t -
            profileD profileMeasure f (profileQuantile profileMeasure f
              (deletedEmpiricalArrival removed clocks t))|}) atTop (𝓝 0))
```

### deletedEmpiricalRemaining

def; [source line 356](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:356)

The normalized total unmarked rate strictly after time `t`. At an
unmarked arrival this is exactly the denominator governing the next gap.

```lean
def deletedEmpiricalRemaining {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (clocks : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ removed, if t < clocks i then w.rate i else 0) / n
```

### deleted_remaining_weak_strict_error

lemma; [source line 362](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:362)

With distinct clocks, passing from weak to strict survival removes at
most the single ringing clock, uniformly over times and deleted sets.

```lean
lemma deleted_remaining_weak_strict_error (w : WeightArray) (n : ℕ)
    (removed : Finset (Fin (n + 1))) (clocks : Fin (n + 1) → ℝ)
    (hinj : Function.Injective clocks) (t : ℝ) :
    |deletedEmpiricalRemaining (w (n + 1)) removed clocks t -
      deletedEmpiricalRemainingGe (w (n + 1)) removed clocks t| ≤
        rowMaxRate w n / (n + 1 : ℕ)
```

### section5_deleted_gap_rate

theorem; [source line 409](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DeletedRace.lean:409)

The actual post-arrival deleted-chain denominator `W_q°/n` converges
uniformly to `D(t_(q/n))`. Weak/strict survival is accounted for explicitly.
This is still a macroscopic rate limit, not a statement about gap moments.

```lean
theorem section5_deleted_gap_rate
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {clocks | ∃ removed : Finset (Fin n), removed.card ≤ r ∧
        ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed clocks t ≤ α ∧
          ε ≤ |deletedEmpiricalRemaining (w n) removed clocks t -
            profileD profileMeasure f (profileQuantile profileMeasure f
              (deletedEmpiricalArrival removed clocks t))|}) atTop (𝓝 0)
```


## Luce/Section5DiscardedCycles.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DiscardedCycles.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Function
open scoped BigOperators
namespace Luce
```

### deep_roots_le_retained_add_excluded

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DiscardedCycles.lean:12)

A discarded root lies in the orbit of an excluded short-cycle vertex.
Charging the whole orbit costs at most its fixed length.

```lean
theorem deep_roots_le_retained_add_excluded {n : ℕ} (R : Equiv.Perm (Fin n))
    (k J : ℕ) (S : Finset (Fin n)) :
    ((deepShellLabels n J).filter (fun v => v ∈ Section5.maximumCycleRoots R k)).card ≤
      retainedDeepCycleCount R k S J +
        (k+1) * shortCycleVertexCount R (k+1) (Finset.univ \ S)
```

### tail_cycles_le_retained_add_excluded

theorem; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DiscardedCycles.lean:59)

```lean
theorem tail_cycles_le_retained_add_excluded {n : ℕ} (R : Equiv.Perm (Fin n))
    (k J : ℕ) (S : Finset (Fin n)) (α : ℝ)
    (hdeep : ∀ v : Fin n, α*n < (v.val : ℝ)+1 → J ≤ terminalShellNumber v) :
    Section5.cycleCount R k - Section5.bulkCycleCount R α k ≤
      retainedDeepCycleCount R k S J +
        (k+1)*shortCycleVertexCount R (k+1) (Finset.univ \ S)
```


## Luce/Section5DiscardedLabels.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DiscardedLabels.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
namespace Luce
```

### retained_labels_complement

theorem; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DiscardedLabels.lean:8)

```lean
theorem retained_labels_complement {n : ℕ} (w : Weights n) (M β δ : ℝ) :
    Finset.univ \ retainedCycleLabels w M β δ =
      (Finset.univ.filter (fun u => M < w.rate u)) ∪
        (Finset.univ.filter (fun u => w.rate u < δ ∧ (u.val : ℝ)+1 ≤ β*n))
```

### excluded_short_vertices_le_high_add_interior_low

theorem; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section5DiscardedLabels.lean:16)

```lean
theorem excluded_short_vertices_le_high_add_interior_low {n : ℕ}
    (w : Weights n) (R : Equiv.Perm (Fin n)) (L : ℕ) (M β δ : ℝ) :
    shortCycleVertexCount R L (Finset.univ \ retainedCycleLabels w M β δ) ≤
      shortCycleVertexCount R L (Finset.univ.filter (fun u => M < w.rate u)) +
      shortCycleVertexCount R L
        (Finset.univ.filter (fun u => w.rate u < δ ∧ (u.val : ℝ)+1 ≤ β*n))
```


## Luce/Section5EarlyDeepSum.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyDeepSum.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### early_deep_expectation_le_shell_sum

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyDeepSum.lean:12)

The target-dependent early cutoff agrees with the shell cutoff.
This bounds the full deep-target sum by the already proved shell costs.

```lean
theorem early_deep_expectation_le_shell_sum {n : ℕ} (w : Weights n)
    (k J : ℕ) (hJ : 1 ≤ J) (S : Finset (Fin n)) :
    (∫ old, ∑ v ∈ deepShellLabels n J, ∑ u ∈ S.filter (fun u => u < v),
      earlyGhostKernel w (k+2) old u v (terminalShellTime v) *
        markedReturnWeight (ghostEntry w (k+2) old) k v u ∂exponentialRace w) ≤
    ∑ j ∈ Finset.Icc J n, ∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostKernel w (k+2) old u v ((j : ℝ) - Real.sqrt j) *
        markedReturnWeight (ghostEntry w (k+2) old) k v u ∂exponentialRace w
```


## Luce/Section5EarlyExponent.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyExponent.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
namespace Luce
```

### half_mean_exponent

theorem; [source line 6](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyExponent.lean:6)

```lean
theorem half_mean_exponent {B q : ℝ} (hB : 0 < B) (hq : 0 ≤ q) (hhalf : 2*q ≤ B) :
    B/8 ≤ (B-q)^2/(2*B)
```

### shell_early_envelope_offset

theorem; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyExponent.lean:13)

The finite window-width offset is absorbed by a cutoff depending only
on the fixed cycle length. The logarithmic time coefficient stays one.

```lean
theorem shell_early_envelope_offset {r h ell : ℝ} (hr : 1 ≤ r) (hell : 0 ≤ ell)
    (hh : 64 ≤ h) (hoff : 2*(ell+1) ≤ Real.exp h) :
    r * Real.exp (-((r*Real.exp h-(r+ell))^2/(2*(r*Real.exp h)))) ≤ Real.exp (1-h)
```


## Luce/Section5EarlyKernel.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyKernel.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Luce
```

### earlyGhostKernel

def; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyKernel.lean:12)

The actual early window probability, with the same null-background
extension as the original ghost kernel.

```lean
def earlyGhostKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i v : Fin n) (s : ℝ) : ℝ :=
  if h : Function.Injective old then earlyGhostEntry w ell old h i v s else 0
```

### earlyGhostKernel_ae_eq_count

theorem; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyKernel.lean:16)

```lean
theorem earlyGhostKernel_ae_eq_count {n : ℕ} (w : Weights n) (ell : ℕ)
    (i v : Fin n) (s : ℝ) :
    (fun old => earlyGhostKernel w ell old i v s) =ᵐ[exponentialRace w]
      (fun old => (expMeasure (w.rate i)).real
        {t | GhostCountWindow ell old v t ∧ t ≤ s})
```

### aestronglyMeasurable_earlyGhostKernel

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyKernel.lean:30)

```lean
theorem aestronglyMeasurable_earlyGhostKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (i v : Fin n) (s : ℝ) :
    AEStronglyMeasurable (fun old => earlyGhostKernel w ell old i v s)
      (exponentialRace w)
```

### earlyGhostKernel_nonneg

theorem; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyKernel.lean:45)

```lean
theorem earlyGhostKernel_nonneg {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i v : Fin n) (s : ℝ) :
    0 ≤ earlyGhostKernel w ell old i v s
```

### earlyGhostKernel_le_ghostEntry

theorem; [source line 51](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyKernel.lean:51)

```lean
theorem earlyGhostKernel_le_ghostEntry {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i v : Fin n) (s : ℝ) :
    earlyGhostKernel w ell old i v s ≤ ghostEntry w ell old i v
```

### integrable_early_return_product

theorem; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyKernel.lean:59)

```lean
theorem integrable_early_return_product {n : ℕ} (w : Weights n) (k : ℕ)
    (v u : Fin n) (s : ℝ) :
    Integrable (fun old => earlyGhostKernel w (k+2) old u v s *
      markedReturnWeight (ghostEntry w (k+2) old) k v u) (exponentialRace w)
```

### early_ghost_return_expectation

theorem; [source line 82](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyKernel.lean:82)

Integrated early contribution of the actual split ghost edge.

```lean
theorem early_ghost_return_expectation {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j k : ℕ) (hshell : (terminalShell n j).Nonempty)
    (hj : (64 + 2 * (k + 2 + 1)) ^ 2 ≤ j) :
    (∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostKernel (w n) (k+2) old u v ((j : ℝ) - Real.sqrt j) *
        markedReturnWeight (ghostEntry (w n) (k+2) old) k v u
      ∂exponentialRace (w n)) ≤
      (2*(k+2)+1 : ℕ)^(k+1) * Real.exp (1 - Real.sqrt j)
```


## Luce/Section5EarlyReturn.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyReturn.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### early_shell_return_expectation

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyReturn.lean:11)

On the rare early-survivor event we may bound even the entire marked
return contribution, before imposing predecessor or retention restrictions.

```lean
theorem early_shell_return_expectation {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j k : ℕ) (hshell : (terminalShell n j).Nonempty)
    (hj : (64 + 2 * (k + 2 + 1)) ^ 2 ≤ j) :
    (∫ old in earlyGhostSurvivorEvent n (shellMax n j hshell) (k+2)
        ((j : ℝ) - Real.sqrt j),
      ∑ v ∈ terminalShell n j, ∑ u : Fin n,
        ghostEntry (w n) (k+2) old u v *
          markedReturnWeight (ghostEntry (w n) (k+2) old) k v u
      ∂exponentialRace (w n)) ≤
      (2*(k+2)+1 : ℕ)^(k+1) * Real.exp (1 - Real.sqrt j)
```


## Luce/Section5EarlyTail.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyTail.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Luce
```

### earlyCycleShellCost

def; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyTail.lean:11)

Expected early marked-return contribution of one nonempty target shell.
An empty shell has zero contribution.

```lean
def earlyCycleShellCost (w : WeightArray) (k n j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
    earlyGhostKernel (w n) (k+2) old u v ((j : ℝ) - Real.sqrt j) *
      markedReturnWeight (ghostEntry (w n) (k+2) old) k v u
    ∂exponentialRace (w n))
```

### earlyCycleShellCost_le

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyTail.lean:17)

```lean
theorem earlyCycleShellCost_le {w : WeightArray} (hnorm : NormalizedWeights w)
    (k n j : ℕ) (hj : (64 + 2 * (k+2+1))^2 ≤ j) :
    earlyCycleShellCost w k n j ≤ ENNReal.ofReal ((2*(k+2)+1 : ℕ)^(k+1) : ℝ) *
      ENNReal.ofReal (Real.exp (1 - Real.sqrt j))
```

### earlyCycleShellTail_le

theorem; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyTail.lean:26)

```lean
theorem earlyCycleShellTail_le {w : WeightArray} (hnorm : NormalizedWeights w)
    (k n J : ℕ) (hJ : (64 + 2 * (k+2+1))^2 ≤ J) :
    nonnegativeTail (earlyCycleShellCost w k) n J ≤
      ENNReal.ofReal ((2*(k+2)+1 : ℕ)^(k+1) : ℝ) *
        ∑' j : ℕ, if J ≤ j then ENNReal.ofReal (Real.exp (1 - Real.sqrt j)) else 0
```

### earlyCycleShellTail_small

theorem; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyTail.lean:40)

Early contributions vanish uniformly in the row. This uniform bound is
a derived estimate; the endpoint shell assumption itself is not strengthened.

```lean
theorem earlyCycleShellTail_small {w : WeightArray} (hnorm : NormalizedWeights w)
    (k : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ n : ℕ, nonnegativeTail (earlyCycleShellCost w k) n J < ε
```

### earlyCycleShellTail_limit

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyTail.lean:56)

```lean
theorem earlyCycleShellTail_limit {w : WeightArray} (hnorm : NormalizedWeights w)
    (k : ℕ) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (earlyCycleShellCost w k) n J)
      atTop) atTop (𝓝 0)
```


## Luce/Section5EarlyWindowEvent.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyWindowEvent.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### earlyGhostSurvivorEvent

def; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyWindowEvent.lean:9)

```lean
def earlyGhostSurvivorEvent (n r ell : ℕ) (s : ℝ) : Set (Fin n → ℝ) :=
  {e | (∑ i, clockSurvivalIndicator s i e) ≤ (r : ℝ)+ell}
```

### measurableSet_earlyGhostSurvivorEvent

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyWindowEvent.lean:12)

```lean
theorem measurableSet_earlyGhostSurvivorEvent (n r ell : ℕ) (s : ℝ) :
    MeasurableSet (earlyGhostSurvivorEvent n r ell s)
```

### survival_sum_add_before_le

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyWindowEvent.lean:17)

```lean
theorem survival_sum_add_before_le {n : ℕ} (e : Fin n → ℝ) {s t : ℝ} (hts : t ≤ s) :
    (∑ i, clockSurvivalIndicator s i e) + (clockBeforeCount e t : ℝ) ≤ n
```

### early_ghost_window_implies_survivor_event

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyWindowEvent.lean:33)

Any early piece of a target ghost window in a shell forces a low
survivor count at the common cutoff, even at coincident clock times.

```lean
theorem early_ghost_window_implies_survivor_event {n j : ℕ}
    (e : Fin n → ℝ) (hinj : Function.Injective e) (hpos : ∀ i, 0 ≤ e i)
    (ell : ℕ) (v : Fin n) (hv : v ∈ terminalShell n j)
    (hshell : (terminalShell n j).Nonempty) {s t : ℝ} (hts : t ≤ s)
    (hwindow : GhostWindowByOrder e hinj ell v t) :
    e ∈ earlyGhostSurvivorEvent n (shellMax n j hshell) ell s
```


## Luce/Section5EarlyWindowProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyWindowProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### early_ghost_shell_probability

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5EarlyWindowProbability.lean:12)

A cutoff depending only on the fixed window width absorbs its finite
offset. No restriction on the rate array is hidden in this cutoff.

```lean
theorem early_ghost_shell_probability {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j ell : ℕ) (hshell : (terminalShell n j).Nonempty)
    (hj : (64 + 2 * (ell + 1)) ^ 2 ≤ j) :
    ((terminalShell n j).card : ℝ) *
      (exponentialRace (w n)).real
        (earlyGhostSurvivorEvent n (shellMax n j hshell) ell
          ((j : ℝ) - Real.sqrt j)) ≤ Real.exp (1 - Real.sqrt j)
```


## Luce/Section5ExceptionalHigh.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalHigh.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set Function
open scoped BigOperators Topology
namespace Luce
```

### high_rate_cycle_vertex_probability

theorem; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalHigh.lean:23)

The single-vertex estimate used in the high-rate proof. The finite
half-mass hypothesis is the one proved eventually from the original assumptions.

```lean
theorem high_rate_cycle_vertex_probability {n : ℕ} (w : Weights n) (k : ℕ) (M : ℝ)
    (hmass : (n : ℝ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => w.rate i ≤ M), w.rate i)
    (v : Fin n) (hv : M < w.rate v) :
    (exponentialRace w).real {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1} ≤
      (2 * w.rate v / n) * (predecessorConstant (k + 1) k : ℝ)
```

### highCycleConstant

def; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalHigh.lean:56)

A uniform constant for the sum over all lengths from 1 through L.

```lean
def highCycleConstant (L : ℕ) : ℕ :=
  2 * ∑ k : Fin L, predecessorConstant (k.val + 1) k.val
```

### high_rate_cycle_vertices_bound

theorem; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalHigh.lean:61)

Quantitative high-rate vertex bound in (1204–1206). The left side counts
vertices in H, not all vertices of cycles which happen to meet H.

```lean
theorem high_rate_cycle_vertices_bound {n : ℕ} (w : Weights n) (L : ℕ) (M : ℝ)
    (hmass : (n : ℝ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => w.rate i ≤ M), w.rate i) :
    (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L
      (Finset.univ.filter (fun v => M < w.rate v)) : ℝ) ∂exponentialRace w) ≤
      (highCycleConstant L : ℝ) *
        ((∑ v ∈ Finset.univ.filter (fun v => M < w.rate v), w.rate v) / n)
```

### highCycleExpectation

def; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalHigh.lean:84)

The actual expectation in the high-rate part of Proposition 5.4.

```lean
def highCycleExpectation (w : WeightArray) (L n : ℕ) (M : ℝ) : ℝ :=
  ∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L
    (Finset.univ.filter (fun v => M < (w n).rate v)) : ℝ) ∂exponentialRace (w n)
```

### highCycleExpectation_nonneg

lemma; [source line 88](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalHigh.lean:88)

```lean
lemma highCycleExpectation_nonneg (w : WeightArray) (L n : ℕ) (M : ℝ) :
    0 ≤ highCycleExpectation w L n M
```

### ProfileLimit.highCycleExpectation_small

theorem; [source line 93](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalHigh.lean:93)

High-rate cycles vanish under exactly the source's normalization and
profile assumptions. Endpoint control is unnecessary for this half.

```lean
theorem ProfileLimit.highCycleExpectation_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) (L : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∀ᶠ n : ℕ in atTop, highCycleExpectation w L n M < ε
```

### ProfileLimit.high_rate_cycles_vanish

theorem; [source line 123](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalHigh.lean:123)

Literal iterated-limit statement in the high-rate half of Proposition
5.4. Eventual upper boundedness is proved before using the real limsup, so
the totalized limsup operation cannot mask an unbounded sequence.

```lean
theorem ProfileLimit.high_rate_cycles_vanish {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) (L : ℕ) :
    Tendsto (fun M : ℝ => limsup (fun n => highCycleExpectation w L n M) atTop)
      atTop (𝓝 0)
```


## Luce/Section5ExceptionalInteraction.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalInteraction.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Function Set
open scoped BigOperators
namespace Luce
```

### OrbitAvoids

def; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalInteraction.lean:18)

Every vertex of the actual orbit avoids H.

```lean
def OrbitAvoids {n : ℕ} (R : Fin n → Fin n) (H : Finset (Fin n)) (v : Fin n) : Prop :=
  ∀ u ∈ periodicOrbit R v, u ∉ H
```

### shortCycleVertexCountAvoiding

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalInteraction.lean:22)

Vertices in S in short cycles whose entire orbit avoids H.

```lean
def shortCycleVertexCountAvoiding {n : ℕ} (R : Fin n → Fin n)
    (L : ℕ) (S H : Finset (Fin n)) : ℕ :=
  (S.filter fun v => minimalPeriod R v ≤ L ∧ OrbitAvoids R H v).card
```

### shortCycleVertexCount_le_high_add_avoiding

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalInteraction.lean:28)

Literal finite charging inequality in source 1231–1237. The sets
need not be disjoint; neither is required invariant under R.

```lean
theorem shortCycleVertexCount_le_high_add_avoiding {n : ℕ}
    (R : Equiv.Perm (Fin n)) (L : ℕ) (S H : Finset (Fin n)) :
    shortCycleVertexCount R L S ≤
      L * shortCycleVertexCount R L H + shortCycleVertexCountAvoiding R L S H
```

### shortCycleVertexCountAvoiding_integrable

lemma; [source line 77](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalInteraction.lean:77)

```lean
lemma shortCycleVertexCountAvoiding_integrable {n : ℕ} (w : Weights n)
    (L : ℕ) (S H : Finset (Fin n)) :
    Integrable (fun clocks => (shortCycleVertexCountAvoiding
      (raceRankPermutation clocks) L S H : ℝ)) (exponentialRace w)
```

### shortCycleVertexCount_expectation_le_high_add_avoiding

theorem; [source line 93](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalInteraction.lean:93)

Integrating the finite orbit count is valid because both counts have
separately proved integrability.

```lean
theorem shortCycleVertexCount_expectation_le_high_add_avoiding {n : ℕ}
    (w : Weights n) (L : ℕ) (S H : Finset (Fin n)) :
    (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ)
      ∂exponentialRace w) ≤
      (L : ℝ) * (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L H : ℝ)
        ∂exponentialRace w) +
      ∫ clocks, (shortCycleVertexCountAvoiding (raceRankPermutation clocks) L S H : ℝ)
        ∂exponentialRace w
```


## Luce/Section5ExceptionalLow.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalLow.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set Function
open scoped BigOperators Topology
namespace Luce
```

### lowCycleExpectation

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalLow.lean:20)

The literal low-rate expectation of the manuscript's V_(n,L).

```lean
def lowCycleExpectation (w : WeightArray) (L n : ℕ) (δ : ℝ) : ℝ :=
  ∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L
    (Finset.univ.filter (fun v => (w n).rate v < δ)) : ℝ) ∂exponentialRace (w n)
```

### lowCycleExpectation_nonneg

lemma; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalLow.lean:24)

```lean
lemma lowCycleExpectation_nonneg (w : WeightArray) (L n : ℕ) (δ : ℝ) :
    0 ≤ lowCycleExpectation w L n δ
```

### ProfileLimit.lowCycleExpectation_bound

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalLow.lean:30)

Quantitative inequality at source 1233–1237. The endpoint hypothesis
places all low labels strictly in the interior. There is no assumption
ε₀<1: if that interval is empty, the label condition proves it empty.

```lean
theorem ProfileLimit.lowCycleExpectation_bound {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) (L : ℕ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ M : ℝ, 0 < M → ∃ K : ℝ, 0 < K ∧
      ∀ δ : ℝ, 0 < δ → δ < γ → ∀ᶠ n : ℕ in atTop,
        lowCycleExpectation w L n δ ≤
          (L : ℝ) * highCycleExpectation w L n M + K * lowRateDensity w n δ
```

### ProfileLimit.lowCycleExpectation_small

theorem; [source line 75](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalLow.lean:75)

Quantified version of the low-rate limit, with the row threshold
chosen after δ, as required by the iterated limit in the manuscript.

```lean
theorem ProfileLimit.lowCycleExpectation_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w)
    (hend : EndpointAssumption w) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n : ℕ in atTop, lowCycleExpectation w L n δ < ε
```

### ProfileLimit.low_rate_cycles_vanish

theorem; [source line 105](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalLow.lean:105)

The literal low-rate iterated limit in Proposition 5.4. Eventual
boundedness and nonnegativity are established before invoking real limsup.

```lean
theorem ProfileLimit.low_rate_cycles_vanish {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w)
    (hend : EndpointAssumption w) (L : ℕ) :
    Tendsto (fun δ : ℝ => limsup (fun n => lowCycleExpectation w L n δ) atTop)
      (𝓝[>] 0) (𝓝 0)
```

### section5_proposition54

theorem; [source line 131](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ExceptionalLow.lean:131)

The whole of Proposition 5.4, under exactly the standing normalization
and the two numbered assumptions. The two counts retain strict rate cutoffs.

```lean
theorem section5_proposition54 (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (hend : EndpointAssumption w) (L : ℕ) :
    Tendsto (fun M : ℝ => limsup (fun n => highCycleExpectation w L n M) atTop)
      atTop (𝓝 0) ∧
    Tendsto (fun δ : ℝ => limsup (fun n => lowCycleExpectation w L n δ) atTop)
      (𝓝[>] 0) (𝓝 0)
```


## Luce/Section5FactorialExpectation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialExpectation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### raceRankPermutation_apply_eq_iff

theorem; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialExpectation.lean:10)

```lean
theorem raceRankPermutation_apply_eq_iff {n : ℕ} (e : Fin n → ℝ)
    (he : Function.Injective e) (i j : Fin n) :
    raceRankPermutation e i = j ↔ raceRank e i = j.val+1
```

### integral_cycleBlockIndicator_eq_rank_probability

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialExpectation.lean:19)

```lean
theorem integral_cycleBlockIndicator_eq_rank_probability {n : ℕ} (w : Weights n)
    (L : ℕ) (m : Fin L → ℕ) (t : Section5.CycleVertex L m ↪ Fin n) :
    (∫ e, Section5.cycleBlockIndicator (raceRankPermutation e) L m t ∂exponentialRace w) =
      (exponentialRace w).real {e | ∀ x, raceRank e (t x) =
        (t (Section5.cycleBlockPermutation L m x)).val+1}
```

### bulk_factorial_expectation_eq_rank_sum

theorem; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialExpectation.lean:46)

The actual bulk joint factorial expectation equals the sum of rank
cylinder probabilities with exactly the original rotational divisor.

```lean
theorem bulk_factorial_expectation_eq_rank_sum {n : ℕ} (w : Weights n)
    (L : ℕ) (m : Fin L → ℕ) (α : ℝ) :
    (∫ e, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation e) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace w) =
    (∑ t : Section5.CycleVertex L m ↪ Fin n,
      if ∀ x, ((t x).val : ℝ)+1 ≤ α*n then
        (exponentialRace w).real {e | ∀ x, raceRank e (t x) =
          (t (Section5.cycleBlockPermutation L m x)).val+1} else 0) /
      ∏ ell : Fin L, ((ell.val+1 : ℕ) : ℝ)^m ell
```


## Luce/Section5FactorialLocal.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialLocal.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
```

### bulk_factorial_expectation_eq_cyclicRaceSum

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialLocal.lean:11)

Relabeling block vertices preserves the actual rank cylinder sum.

```lean
theorem bulk_factorial_expectation_eq_cyclicRaceSum {n r : ℕ} (w : Weights n)
    (L : ℕ) (m : Fin L → ℕ) (α : ℝ) (e : Section5.CycleVertex L m ≃ Fin r) :
    (∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace w) =
    cyclicRaceSum w α (e.symm.trans ((Section5.cycleBlockPermutation L m).trans e))
      (fun _ => 1) / ∏ ell : Fin L, ((ell.val+1 : ℕ) : ℝ)^m ell
```

### bulk_factorial_tendsto_block_integral

theorem; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialLocal.lean:40)

Bulk joint factorial moments converge to the literal block cyclic
integral. Factoring this integral into individual cycle intensities is a
separate remaining obligation. The positive-size premise selects a moment,
and is not a restriction on the rate model.

```lean
theorem bulk_factorial_tendsto_block_integral (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (m : Fin L → ℕ) (r : ℕ) (hr : 0 < r)
    (e : Section5.CycleVertex L m ≃ Fin r) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace (w n)) atTop
      (𝓝 ((∫ x in cyclicBulkCube r α, ∏ a,
        cyclicProfileDensity f (x a)
          (x ((e.symm.trans ((Section5.cycleBlockPermutation L m).trans e)) a))) /
          ∏ ell : Fin L, ((ell.val+1 : ℕ) : ℝ)^m ell))
```

### factorialBlockPermutation

def; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialLocal.lean:60)

Canonical indexing of the original block vertices; no representation
witness is an input to the resulting moment limit.

```lean
def factorialBlockPermutation (L : ℕ) (m : Fin L → ℕ) :
    Equiv.Perm (Fin (Fintype.card (Section5.CycleVertex L m))) :=
  (Fintype.equivFin (Section5.CycleVertex L m)).symm.trans
    ((Section5.cycleBlockPermutation L m).trans
      (Fintype.equivFin (Section5.CycleVertex L m)))
```

### bulk_factorial_tendsto_canonical_block_integral

theorem; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialLocal.lean:66)

```lean
theorem bulk_factorial_tendsto_canonical_block_integral
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (m : Fin L → ℕ)
    (hm : 0 < Fintype.card (Section5.CycleVertex L m)) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace (w n)) atTop
      (𝓝 ((∫ x in cyclicBulkCube (Fintype.card (Section5.CycleVertex L m)) α,
        ∏ a, cyclicProfileDensity f (x a) (x (factorialBlockPermutation L m a))) /
          ∏ ell : Fin L, ((ell.val+1 : ℕ) : ℝ)^m ell))
```

### bulk_factorial_expectation_zero

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialLocal.lean:81)

The zero-order joint moment is exactly one in every original row.

```lean
theorem bulk_factorial_expectation_zero {n : ℕ} (w : Weights n)
    (L : ℕ) (α : ℝ) :
    (∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial 0 : ℝ)
      ∂exponentialRace w) = 1
```


## Luce/Section5FactorialMoments.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialMoments.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
```

### bulk_joint_factorial_moments

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialMoments.lean:11)

Every bulk joint falling-factorial moment has the independent-Poisson
value specified by the manuscript's literal truncated cycle intensities.
There is no endpoint, moment, boundedness, or integrability input.

```lean
theorem bulk_joint_factorial_moments (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (m : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, ∏ ell : Fin L,
      ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial (m ell) : ℝ)
      ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell : Fin L, bulkCycleTraceIntensity f α ell.val ^ m ell))
```

### bulk_cycle_first_moment

theorem; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialMoments.lean:35)

In particular the original expected bulk cycle count converges to the
literal truncated cyclic intensity.

```lean
theorem bulk_cycle_first_moment (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (k : ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z,
      (Section5.bulkCycleCount (raceRankPermutation z) α k : ℝ)
      ∂exponentialRace (w n)) atTop (𝓝 (bulkCycleTraceIntensity f α k))
```

### bulk_cycle_trace_integrable

theorem; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialMoments.lean:45)

```lean
theorem bulk_cycle_trace_integrable {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (k : ℕ) {α : ℝ} (hα : α < 1) :
    IntegrableOn (cycleTraceIntegrand f k) (cyclicBulkCube (k+1) α)
```

### bulk_cycle_intensity_nonneg

theorem; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialMoments.lean:54)

```lean
theorem bulk_cycle_intensity_nonneg (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (k : ℕ) (α : ℝ) (hα : α < 1) :
    0 ≤ bulkCycleTraceIntensity f α k
```


## Luce/Section5FactorialPolynomials.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialPolynomials.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
```

### bulk_factorial_polynomial_limit

theorem; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialPolynomials.lean:10)

Finite products of factorial polynomials converge using only the
proved bulk joint moments. Signed coefficients are allowed.

```lean
theorem bulk_factorial_polynomial_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L r : ℕ) (p : Fin L → Fin r → ℕ) (c : Fin L → Fin r → ℝ)
    (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, ∏ ell : Fin L, ∑ j : Fin r,
      c ell j * ((Section5.bulkCycleCount (raceRankPermutation z) α ell.val).descFactorial
        (p ell j) : ℝ) ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell : Fin L, ∑ j : Fin r,
        c ell j * bulkCycleTraceIntensity f α ell.val ^ p ell j))
```

### bulk_count_sieve_expectation_limit

theorem; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialPolynomials.lean:44)

The actual joint point-probability sieve has the prescribed limiting
finite exponential expansion. Removing K still requires its error bound.

```lean
theorem bulk_count_sieve_expectation_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L K : ℕ) (q : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, countVectorSieve q K
      (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val)
      ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell : Fin L, ∑ j : Fin (K+1),
        (-1 : ℝ)^j.val * bulkCycleTraceIntensity f α ell.val ^ (q ell+j.val) /
          (((q ell).factorial : ℝ) * (j.val.factorial : ℝ))))
```


## Luce/Section5FactorialSieve.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open scoped BigOperators
namespace Luce
```

### zeroCountSieve

def; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:9)

Finite inclusion-exclusion polynomial for the zero-count event.

```lean
def zeroCountSieve (K n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), (-1 : ℝ)^j * (n.choose j : ℝ)
```

### zeroCountSieve_succ

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:12)

```lean
theorem zeroCountSieve_succ (K n : ℕ) :
    zeroCountSieve K (n+1) = (-1 : ℝ)^K * (n.choose K : ℝ)
```

### zeroCountSieve_zero

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:17)

```lean
theorem zeroCountSieve_zero (K : ℕ) : zeroCountSieve K 0 = 1
```

### zeroCountSieve_error

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:24)

The error is bounded by the next binomial moment. No distributional
or moment assumption is used in this pointwise inequality.

```lean
theorem zeroCountSieve_error (K n : ℕ) :
    |zeroCountSieve K n - (if n = 0 then (1 : ℝ) else 0)| ≤ (n.choose (K+1) : ℝ)
```

### countSieve

def; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:37)

Finite sieve for an arbitrary count value.

```lean
def countSieve (q K n : ℕ) : ℝ := (n.choose q : ℝ) * zeroCountSieve K (n-q)
```

### choose_mul_zero_indicator

theorem; [source line 39](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:39)

```lean
theorem choose_mul_zero_indicator (q n : ℕ) :
    (n.choose q : ℝ) * (if n-q = 0 then 1 else 0) =
      (if n = q then 1 else 0)
```

### countSieve_error

theorem; [source line 49](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:49)

```lean
theorem countSieve_error (q K n : ℕ) :
    |countSieve q K n - (if n = q then (1 : ℝ) else 0)| ≤
      (n.choose q : ℝ) * ((n-q).choose (K+1) : ℝ)
```

### choose_product_eq_factorial_ratio

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:56)

```lean
theorem choose_product_eq_factorial_ratio (q j n : ℕ) :
    (n.choose q : ℝ) * ((n-q).choose j : ℝ) =
      (n.descFactorial (q+j) : ℝ) / ((q.factorial : ℝ) * (j.factorial : ℝ))
```

### countSieve_eq_factorial_sum

theorem; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:69)

```lean
theorem countSieve_eq_factorial_sum (q K n : ℕ) :
    countSieve q K n = ∑ j ∈ Finset.range (K+1),
      (-1 : ℝ)^j * (n.descFactorial (q+j) : ℝ) /
        ((q.factorial : ℝ) * (j.factorial : ℝ))
```

### countSieve_error_factorial

theorem; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:80)

```lean
theorem countSieve_error_factorial (q K n : ℕ) :
    |countSieve q K n - (if n = q then (1 : ℝ) else 0)| ≤
      (n.descFactorial (q+(K+1)) : ℝ) /
        ((q.factorial : ℝ) * ((K+1).factorial : ℝ))
```

### countVectorSieve

def; [source line 86](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:86)

```lean
def countVectorSieve {L : ℕ} (q : Fin L → ℕ) (K : ℕ) (x : Fin L → ℕ) : ℝ :=
  ∏ ell, countSieve (q ell) K (x ell)
```

### countVectorSieve_error

theorem; [source line 92](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FactorialSieve.lean:92)

A joint point probability is approximated by a finite product of
factorial polynomials. The error involves only higher joint factorial
moments, all of which are already proved for the bulk cycle vector.

```lean
theorem countVectorSieve_error {L : ℕ} (q : Fin L → ℕ) (K : ℕ) (x : Fin L → ℕ) :
    |countVectorSieve q K x - (if x = q then (1 : ℝ) else 0)| ≤
      (∏ ell, (1 + (x ell |>.descFactorial (q ell+(K+1)) : ℝ) /
        (((q ell).factorial : ℝ) * ((K+1).factorial : ℝ)))) - 1
```


## Luce/Section5FiniteCover.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteCover.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open scoped BigOperators
namespace Luce
```

### finite_cover_sum_le

theorem; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteCover.lean:10)

Nonnegative weights on a finite covered set can be charged to all
covering sets. Overlaps only enlarge the upper bound.

```lean
theorem finite_cover_sum_le {α ι : Type*} [Fintype α] [DecidableEq α]
    (S S₀ : Finset α) (I : Finset ι) (blocks : ι → Finset α) (F : α → ℝ)
    (hF : ∀ u, 0 ≤ F u)
    (hcover : ∀ u ∈ S, u ∈ S₀ ∨ ∃ r ∈ I, u ∈ blocks r) :
    (∑ u ∈ S, F u) ≤ (∑ u ∈ S₀, F u) + ∑ r ∈ I, ∑ u ∈ blocks r, F u
```


## Luce/Section5FiniteInsertion.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Luce
```

### ghostOrderKernel

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:22)

Probability of the actual open order-statistic window J_j. The arbitrary
zero extension at tied backgrounds is on a proved null set.

```lean
def ghostOrderKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i j : Fin n) : ℝ≥0∞ :=
  if h : Function.Injective old then
    expMeasure (w.rate i) {t | GhostWindowByOrder old h ell j t}
  else 0
```

### measurableSet_ghostWindowByOrder

lemma; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:28)

```lean
lemma measurableSet_ghostWindowByOrder {n : ℕ} (old : Fin n → ℝ)
    (h : Function.Injective old) (ell : ℕ) (j : Fin n) :
    MeasurableSet {t | GhostWindowByOrder old h ell j t}
```

### exponential_avoids_background

lemma; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:36)

Every fixed background has only finitely many boundary times; the
independent exponential insertion avoids all of them almost surely.

```lean
lemma exponential_avoids_background {n : ℕ} (old : Fin n → ℝ) (r : ℝ) :
    ∀ᵐ t ∂expMeasure r, ∀ i, t ≠ old i
```

### ghostOrderKernel_eq_count

lemma; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:42)

```lean
lemma ghostOrderKernel_eq_count {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old)
    (hnonneg : ∀ i, 0 ≤ old i) (i j : Fin n) :
    ghostOrderKernel w ell old i j = ghostCountKernel w ell old i j
```

### exponentialRace_nonnegative_background

lemma; [source line 51](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:51)

```lean
lemma exponentialRace_nonnegative_background {n : ℕ} (w : Weights n) :
    ∀ᵐ old ∂exponentialRace w, ∀ i, 0 ≤ old i
```

### ghostOrderKernel_ae_eq_count

lemma; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:59)

```lean
lemma ghostOrderKernel_ae_eq_count {n : ℕ} (w : Weights n) (ell : ℕ) :
    ∀ᵐ old ∂exponentialRace w, ∀ i j,
      ghostOrderKernel w ell old i j = ghostCountKernel w ell old i j
```

### aemeasurable_ghostOrderKernel

lemma; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:66)

```lean
lemma aemeasurable_ghostOrderKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (i j : Fin n) :
    AEMeasurable (fun old => ghostOrderKernel w ell old i j) (exponentialRace w)
```

### ghostOrderKernel_le_one

lemma; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:73)

The kernel is genuinely a probability, including at tied backgrounds.

```lean
lemma ghostOrderKernel_le_one {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i j : Fin n) : ghostOrderKernel w ell old i j ≤ 1
```

### ghostOrderKernel_eq_density

theorem; [source line 83](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:83)

Density interpretation of the original kernel. This is the literal
integral defining p_(i,j), rather than a kernel with an assumed bound.

```lean
theorem ghostOrderKernel_eq_density {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i j : Fin n) :
    ghostOrderKernel w ell old i j =
      ∫⁻ t in {t | GhostWindowByOrder old hinj ell j t},
        exponentialPDF (w.rate i) t
```

### finite_insertion_path_ennreal

theorem; [source line 95](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:95)

Lemma 5.3 in nonnegative integral form, with explicit K_(ell,m).
It holds for all n and all positive rates, without profile/endpoint/normalization
assumptions. The endpoint v can also be one of the distinct source vertices.

```lean
theorem finite_insertion_path_ennreal {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    (∫⁻ old,
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, ghostOrderKernel w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
      ∂exponentialRace w) ≤ ((2 * (ell + m + 2) + 1) ^ m : ℕ)
```

### ghostEntry

def; [source line 121](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:121)

Real-valued p_(i,j) from `eq:ghost-window`. Finiteness follows from its
probability bound, so conversion from ENNReal cannot discard an infinity.

```lean
def ghostEntry {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (ghostOrderKernel w ell old i j).toReal
```

### ghostWindowByOrder_pos

lemma; [source line 127](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:127)

The paper's time windows lie in the positive half-line whenever the
background clocks are nonnegative.

```lean
lemma ghostWindowByOrder_pos {n : ℕ} (old : Fin n → ℝ)
    (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (ell : ℕ) (j : Fin n) {t : ℝ} (ht : GhostWindowByOrder old hinj ell j t) :
    0 < t
```

### ghostEntry_eq_density_integral

theorem; [source line 138](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:138)

Exact equality with the original real density integral, together with
its integrability. This closes the representational bridge for p_(i,j).

```lean
theorem ghostEntry_eq_density_integral {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old)
    (hnonneg : ∀ i, 0 ≤ old i) (i j : Fin n) :
    IntegrableOn (fun t => w.rate i * Real.exp (-(w.rate i * t)))
      {t | GhostWindowByOrder old hinj ell j t} ∧
    ghostEntry w ell old i j =
      ∫ t in {t | GhostWindowByOrder old hinj ell j t},
        w.rate i * Real.exp (-(w.rate i * t))
```

### ghostEntry_mem_Icc

lemma; [source line 166](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:166)

```lean
lemma ghostEntry_mem_Icc {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i j : Fin n) : ghostEntry w ell old i j ∈ Icc (0 : ℝ) 1
```

### ghostPathSum

def; [source line 173](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:173)

Source integrand with the ordered source tuple and final edge exposed.

```lean
def ghostPathSum {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
    ∏ a, ghostOrderKernel w ell old (u a)
      ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
```

### aemeasurable_ghostPathSum

lemma; [source line 179](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:179)

```lean
lemma aemeasurable_ghostPathSum {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    AEMeasurable (ghostPathSum (m := m) w ell v) (exponentialRace w)
```

### ghostPathSum_ne_top

lemma; [source line 186](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:186)

```lean
lemma ghostPathSum_ne_top {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) : ghostPathSum (m := m) w ell v old ≠ ⊤
```

### ghostPathSum_toReal

lemma; [source line 195](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:195)

```lean
lemma ghostPathSum_toReal {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) :
    (ghostPathSum (m := m) w ell v old).toReal =
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, ghostEntry w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
```

### finite_insertion_path_integrable

theorem; [source line 211](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:211)

Integrability is proved before using the real-valued expectation.
The finite ENNReal estimate prevents a totalized integral from hiding a gap.

```lean
theorem finite_insertion_path_integrable {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    Integrable (fun old =>
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, ghostEntry w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)) (exponentialRace w)
```

### finite_insertion_path

theorem; [source line 226](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:226)

Lemma 5.3, exactly as a real expectation of products of the paper's
window probabilities, with K_(ell,m) = (2*(ell+m+2)+1)^m.
The result also includes the harmless empty-path case m=0.

```lean
theorem finite_insertion_path {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    (∫ old,
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, ghostEntry w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
      ∂exponentialRace w) ≤ ((2 * (ell + m + 2) + 1) ^ m : ℕ)
```

### ghostCountKernel_row_bound

theorem; [source line 246](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:246)

Integrating the proved window multiplicity gives the row bound
`eq:ghost-row-bound`. The background is fixed throughout the calculation.

```lean
theorem ghostCountKernel_row_bound {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i : Fin n) :
    ∑ j, ghostCountKernel w ell old i j ≤ ((2 * ell + 1 : ℕ) : ℝ≥0∞)
```

### ghostEntry_row_bound

theorem; [source line 273](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteInsertion.lean:273)

The paper's real row bound for its actual open time windows. Positive
backgrounds in the manuscript satisfy the exposed nonnegativity condition;
that condition also holds almost surely under the actual race law.

```lean
theorem ghostEntry_row_bound {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ old i) (i : Fin n) :
    ∑ j, ghostEntry w ell old i j ≤ (2 * ell + 1 : ℕ)
```


## Luce/Section5FiniteShellCosts.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteShellCosts.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Luce
```

### finite_nonnegative_sum_le_tail

theorem; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteShellCosts.lean:8)

```lean
theorem finite_nonnegative_sum_le_tail (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (J n : ℕ) :
    ENNReal.ofReal (∑ j ∈ Finset.Icc J n, f j) ≤
      ∑' j : ℕ, if J ≤ j then ENNReal.ofReal (f j) else 0
```

### early_finite_shell_sum_le_tail

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteShellCosts.lean:19)

```lean
theorem early_finite_shell_sum_le_tail (w : WeightArray) (k n J : ℕ) :
    ENNReal.ofReal (∑ j ∈ Finset.Icc J n, ∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostKernel (w n) (k+2) old u v ((j : ℝ) - Real.sqrt j) *
        markedReturnWeight (ghostEntry (w n) (k+2) old) k v u ∂exponentialRace (w n)) ≤
      nonnegativeTail (earlyCycleShellCost w k) n J
```

### buffered_finite_shell_sum_le_tail

theorem; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteShellCosts.lean:35)

```lean
theorem buffered_finite_shell_sum_le_tail (w : WeightArray) (n J : ℕ) (hJ : 2 ≤ J) :
    ENNReal.ofReal (∑ r ∈ Finset.Icc J n, if hs : (terminalShell n r).Nonempty then
      Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0) ≤
      nonnegativeTail (bufferedShellExpCost w) n J
```


## Luce/Section5FiniteStatistic.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteStatistic.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### integrable_race_permutation_statistic

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteStatistic.lean:11)

Every real statistic of the actual finite race permutation is
integrable. The bound is a constructed finite sum, not a moment input.

```lean
theorem integrable_race_permutation_statistic {n : ℕ} (w : Weights n)
    (F : Equiv.Perm (Fin n) → ℝ) :
    Integrable (fun e => F (raceRankPermutation e)) (exponentialRace w)
```


## Luce/Section5FiniteTaylor.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteTaylor.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators
namespace Luce
```

### raceGapStart_eq_consecutiveGapLower

lemma; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteTaylor.lean:19)

```lean
lemma raceGapStart_eq_consecutiveGapLower {m : ℕ} (c : Fin m → ℝ)
    (hc : Injective c) (q : Fin m) :
    raceGapStart c q = consecutiveGapLower c hc q
```

### raceGapDuration_eq_normalized_div_rate

lemma; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteTaylor.lean:24)

```lean
lemma raceGapDuration_eq_normalized_div_rate {m : ℕ} (w : Weights m)
    (c : Fin m → ℝ) (hc : Injective c) (q : Fin m) :
    arrivalTime c hc q - consecutiveGapLower c hc q =
      raceNormalizedGaps w c q / raceGapRate w c q
```

### raceNormalizedGaps_nonneg

lemma; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteTaylor.lean:32)

```lean
lemma raceNormalizedGaps_nonneg {m : ℕ} (w : Weights m)
    (c : Fin m → ℝ) (hc : Injective c) (hpos : ∀ i, 0 ≤ c i) (q : Fin m) :
    0 ≤ raceNormalizedGaps w c q
```

### deletedGapKernel_eq_normalizedGapMass

lemma; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteTaylor.lean:40)

```lean
lemma deletedGapKernel_eq_normalizedGapMass {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hold : Injective old)
    (hpos : ∀ i, 0 ≤ old i) (i : Fin n) (q : Fin (Finset.univ \ removed).card) :
    (deletedGapKernel w removed old i q.val).toReal =
      exponentialGapMass (w.rate i)
        (raceGapStart (compactDeletedClocks removed old) q)
        (raceNormalizedGaps (compactDeletedWeights w removed) (compactDeletedClocks removed old) q /
          raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) q)
```

### markedGap_taylor_pointwise

theorem; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteTaylor.lean:55)

The pointwise rescaled Taylor remainder, with the source's actual
deleted gap masses and coefficients. No probability or conditional law is
assumed here. The raw gap length is replaced using its proved identity.

```lean
theorem markedGap_taylor_pointwise {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n)
    (q : Fin r → Fin (Finset.univ \ removed).card) {b M : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hM : 0 ≤ M) (huM : ∀ a, w.rate (u a) ≤ M)
    (hW : ∀ σ : Equiv.Perm (Fin (Finset.univ \ removed).card), ∀ a,
      b * n ≤ orderedRemainingRate (compactDeletedWeights w removed) σ (q a))
    (old : Fin n → ℝ) (hold : Injective old) (hpos : ∀ i, 0 ≤ old i) :
    |(n : ℝ) ^ r * (∏ a, (deletedGapKernel w removed old (u a) (q a).val).toReal) -
      markedGapCoefficient w removed u q old * (∏ a, markedNormalizedGaps w removed q old a)| ≤
      ((M / b) ^ (r + 1) / n) *
        ((∑ a, markedNormalizedGaps w removed q old a) * ∏ a, markedNormalizedGaps w removed q old a)
```

### markedGap_taylor_expectation

theorem; [source line 85](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteTaylor.lean:85)

The finite Taylor error after averaging the actual deleted race.
Distinct gaps enter only through their proved Exp(1) mixed moments.

```lean
theorem markedGap_taylor_expectation {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n)
    (q : Fin r ↪ Fin (Finset.univ \ removed).card) {b M : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hM : 0 ≤ M) (huM : ∀ a, w.rate (u a) ≤ M)
    (hW : ∀ σ : Equiv.Perm (Fin (Finset.univ \ removed).card), ∀ a,
      b * n ≤ orderedRemainingRate (compactDeletedWeights w removed) σ (q a)) :
    Integrable (fun old => markedGapCoefficient w removed u q old *
      ∏ a, markedNormalizedGaps w removed q old a) (exponentialRace w) ∧
    |(n : ℝ) ^ r * (∫ old, ∏ a, (deletedGapKernel w removed old (u a) (q a).val).toReal
        ∂exponentialRace w) -
      (∫ old, markedGapCoefficient w removed u q old *
        ∏ a, markedNormalizedGaps w removed q old a ∂exponentialRace w)| ≤
      (2 * (r : ℝ) / n) * (M / b) ^ (r + 1)
```

### markedRankCylinder_taylor_expectation

theorem; [source line 143](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FiniteTaylor.lean:143)

Source 1035–1048, finite quantitative version for the actual sorted
marked-rank probability. The lower-rate bound is a finite reservoir input;
the main asymptotic theorem discharges it from the original profile limit.

```lean
theorem markedRankCylinder_taylor_expectation {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r ↪ Fin (Finset.univ \ Finset.univ.image u).card)
    (hq : StrictMono (fun a => (q a).val)) (hindex : ∀ a, (q a).val + a.val = (j a).val)
    {b M : ℝ} (hn : 0 < n) (hb : 0 < b) (hM : 0 ≤ M) (huM : ∀ a, w.rate (u a) ≤ M)
    (hW : ∀ σ : Equiv.Perm (Fin (Finset.univ \ Finset.univ.image u).card), ∀ a,
      b * n ≤ orderedRemainingRate (compactDeletedWeights w (Finset.univ.image u)) σ (q a)) :
    |(n : ℝ) ^ r * (exponentialRace w).real {old | MarkedRankCylinder u j old} -
      (∫ old, markedGapCoefficient w (Finset.univ.image u) u q old *
        ∏ a, markedNormalizedGaps w (Finset.univ.image u) q old a ∂exponentialRace w)| ≤
      (2 * (r : ℝ) / n) * (M / b) ^ (r + 1)
```


## Luce/Section5FullPointProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FullPointProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators Topology
namespace Luce
```

### EndpointShellAssumption.cycle_point_indicator_limit

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FullPointProbability.lean:11)

Full cycle-count point probabilities, after the manuscript's endpoint
cutoff removal. The shell assumption supplies expectation tightness through
its proved theorem, not through an additional hypothesis.

```lean
theorem EndpointShellAssumption.cycle_point_indicator_limit
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) :
    Tendsto (fun n => ∫ z,
      (if cycleCountVector L (raceRankPermutation z) = q then (1 : ℝ) else 0)
      ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell, Real.exp (-cycleTraceIntensity f ell.val) *
        cycleTraceIntensity f ell.val ^ q ell / ((q ell).factorial : ℝ)))
```

### cycle_point_indicator_integral

theorem; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FullPointProbability.lean:52)

```lean
theorem cycle_point_indicator_integral {n : ℕ} (w : Weights n)
    (L : ℕ) (q : Fin L → ℕ) :
    (∫ z, (if cycleCountVector L (raceRankPermutation z) = q then (1 : ℝ) else 0)
      ∂exponentialRace w) =
      (exponentialRace w).real {z | cycleCountVector L (raceRankPermutation z) = q}
```

### cycleVectorPoissonLaw_real_singleton

theorem; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FullPointProbability.lean:64)

```lean
theorem cycleVectorPoissonLaw_real_singleton {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (L : ℕ) (q : Fin L → ℕ) :
    (cycleVectorPoissonLaw f L).real {q} =
      ∏ ell, Real.exp (-cycleTraceIntensity f ell.val) *
        cycleTraceIntensity f ell.val ^ q ell / ((q ell).factorial : ℝ)
```

### EndpointShellAssumption.cycle_point_probability_limit

theorem; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section5FullPointProbability.lean:76)

```lean
theorem EndpointShellAssumption.cycle_point_probability_limit
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) :
    Tendsto (fun n => (exponentialRace (w n)).real
      {z | cycleCountVector L (raceRankPermutation z) = q}) atTop
      (𝓝 ((cycleVectorPoissonLaw f L).real {q}))
```


## Luce/Section5GapCoefficient.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators
namespace Luce
```

### raceGapStart

def; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:17)

```lean
def raceGapStart {n : ℕ} (c : Fin n → ℝ) (q : Fin n) : ℝ :=
  previousOrderedTime (fun k => c (raceDraw c k)) q
```

### raceGapRate

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:20)

```lean
def raceGapRate {n : ℕ} (w : Weights n) (c : Fin n → ℝ) (q : Fin n) : ℝ :=
  orderedRemainingRate w (raceDraw c) q
```

### measurable_raceGapStart

lemma; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:23)

```lean
lemma measurable_raceGapStart {n : ℕ} (q : Fin n) :
    Measurable (fun c : Fin n → ℝ => raceGapStart c q)
```

### measurable_raceGapRate

lemma; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:36)

```lean
lemma measurable_raceGapRate {n : ℕ} (w : Weights n) (q : Fin n) :
    Measurable (fun c : Fin n → ℝ => raceGapRate w c q)
```

### markedGapCoefficient

def; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:43)

```lean
def markedGapCoefficient {n r : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (u : Fin r → Fin n) (q : Fin r → Fin (Finset.univ \ removed).card)
    (old : Fin n → ℝ) : ℝ :=
  ∏ a, rateKernel (raceGapStart (compactDeletedClocks removed old) (q a)) (w.rate (u a)) /
    (raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) (q a) / n)
```

### markedNormalizedGaps

def; [source line 49](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:49)

```lean
def markedNormalizedGaps {n r : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (q : Fin r → Fin (Finset.univ \ removed).card) (old : Fin n → ℝ) : Fin r → ℝ :=
  fun a => raceNormalizedGaps (compactDeletedWeights w removed)
    (compactDeletedClocks removed old) (q a)
```

### measurable_markedGapCoefficient

lemma; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:54)

```lean
lemma measurable_markedGapCoefficient {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n)
    (q : Fin r → Fin (Finset.univ \ removed).card) :
    Measurable (markedGapCoefficient w removed u q)
```

### measurable_markedNormalizedGaps

lemma; [source line 67](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:67)

```lean
lemma measurable_markedNormalizedGaps {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r → Fin (Finset.univ \ removed).card) :
    Measurable (markedNormalizedGaps w removed q)
```

### measurePreserving_markedNormalizedGaps

theorem; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:76)

```lean
theorem measurePreserving_markedNormalizedGaps {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card) :
    MeasurePreserving (markedNormalizedGaps w removed q)
      (exponentialRace w) (standardGapLaw r)
```

### integrable_markedNormalizedGaps_mixed

theorem; [source line 83](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:83)

```lean
theorem integrable_markedNormalizedGaps_mixed {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card)
    (p : Fin r → ℕ) :
    Integrable (fun old => ∏ a, markedNormalizedGaps w removed q old a ^ p a)
      (exponentialRace w)
```

### integral_markedNormalizedGaps_mixed

theorem; [source line 91](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:91)

```lean
theorem integral_markedNormalizedGaps_mixed {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card)
    (p : Fin r → ℕ) :
    (∫ old, ∏ a, markedNormalizedGaps w removed q old a ^ p a ∂exponentialRace w) =
      ∏ a, ((p a).factorial : ℝ)
```

### integral_markedNormalizedGaps_prod

theorem; [source line 104](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:104)

```lean
theorem integral_markedNormalizedGaps_prod {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card) :
    (∫ old, ∏ a, markedNormalizedGaps w removed q old a ∂exponentialRace w) = 1
```

### integral_markedNormalizedGaps_prod_sq

theorem; [source line 109](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:109)

```lean
theorem integral_markedNormalizedGaps_prod_sq {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card) :
    (∫ old, (∏ a, markedNormalizedGaps w removed q old a) ^ 2 ∂exponentialRace w) =
      (2 : ℝ) ^ r
```

### integrable_markedNormalizedGaps_taylorEnvelope

theorem; [source line 116](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:116)

```lean
theorem integrable_markedNormalizedGaps_taylorEnvelope {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card) :
    Integrable (fun old => (∑ a, markedNormalizedGaps w removed q old a) *
      ∏ a, markedNormalizedGaps w removed q old a) (exponentialRace w)
```

### integral_markedNormalizedGaps_taylorEnvelope

theorem; [source line 123](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficient.lean:123)

```lean
theorem integral_markedNormalizedGaps_taylorEnvelope {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card) :
    (∫ old, (∑ a, markedNormalizedGaps w removed q old a) *
      ∏ a, markedNormalizedGaps w removed q old a ∂exponentialRace w) = 2 * (r : ℝ)
```


## Luce/Section5GapCoefficientLimit.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficientLimit.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped ENNReal BigOperators Topology
namespace Luce
```

### deletedEmpiricalRemaining_lower_of_reservoir

lemma; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficientLimit.lean:20)

Count arrived unmarked labels before applying the reservoir.

```lean
lemma deletedEmpiricalRemaining_lower_of_reservoir {n r : ℕ} (w : Weights n)
    (hn : 0 < n) (α B : ℝ)
    (hrem : ∀ gone : Finset (Fin n), (gone.card : ℝ) ≤ α * n + r →
      B * n ≤ ∑ i ∈ Finset.univ \ gone, w.rate i)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (t : ℝ)
    (hr : removed.card ≤ r) (ht : deletedEmpiricalArrival removed old t ≤ α) :
    B ≤ deletedEmpiricalRemaining w removed old t
```

### ProfileLimit.deleted_remaining_uniform_lower

theorem; [source line 51](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficientLimit.lean:51)

A single positive constant bounds all bulk deleted denominators.

```lean
theorem ProfileLimit.deleted_remaining_uniform_lower {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop,
      ∀ removed : Finset (Fin n), removed.card ≤ r →
        ∀ old : Fin n → ℝ, ∀ t : ℝ, deletedEmpiricalArrival removed old t ≤ α →
          b ≤ deletedEmpiricalRemaining (w n) removed old t
```

### deletedGapCoefficientError

def; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficientLimit.lean:64)

The exact scalar error at a deleted time, with its own empirical rank.

```lean
def deletedGapCoefficientError {n : ℕ} (w : Weights n) (f : ℝ → ℝ)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (t a : ℝ) : ℝ :=
  |rateKernel t a / deletedEmpiricalRemaining w removed old t -
    rateKernel (profileQuantile profileMeasure f (deletedEmpiricalArrival removed old t)) a /
      profileD profileMeasure f (profileQuantile profileMeasure f
        (deletedEmpiricalArrival removed old t))|
```

### DeletedCoefficientBad

def; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficientLimit.lean:73)

The bad event quantifies over every deletion, eligible time and bounded
nonnegative rate; there are no probabilistic hypotheses in this predicate.

```lean
def DeletedCoefficientBad {n : ℕ} (w : Weights n) (f : ℝ → ℝ)
    (r : ℕ) (α M ε : ℝ) (old : Fin n → ℝ) : Prop :=
  ∃ removed : Finset (Fin n), removed.card ≤ r ∧
    ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed old t ≤ α ∧
      ∃ a ∈ Icc (0 : ℝ) M, ε ≤ deletedGapCoefficientError w f removed old t a
```

### section5_uniform_deleted_gap_coefficient

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapCoefficientLimit.lean:81)

Uniform scalar convergence. The target uses the deleted empirical
rank; the small deterministic shift to the prescribed full rank is separate.

```lean
theorem section5_uniform_deleted_gap_coefficient
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {old | DeletedCoefficientBad (w n) f r α M ε old}) atTop (𝓝 0)
```


## Luce/Section5GapExpectation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapExpectation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace Luce
```

### integral_error_mul_le

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapExpectation.lean:24)

A bounded error, small off a measurable event, can be multiplied by
an unbounded nonnegative random variable with integrable square. The
truncation parameter `L` is arbitrary and strictly positive.

```lean
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
        C / L * (∫ x, Y x ^ 2 ∂μ) + C * L * μ.real A
```

### uniform_integral_error_mul_small

theorem; [source line 83](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapExpectation.lean:83)

Uniform expectation transfer on varying probability spaces and varying
finite configurations. The moment assumptions are explicitly stated and
will be supplied by the exact selected-gap law, not inferred from weak
convergence. This lemma is only an analytic step toward Lemma 5.2.

```lean
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
      (∫ x, |u n i x| * Y n i x ∂μ n) < ε
```

### abs_integral_coefficient_mul_sub_le

lemma; [source line 137](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapExpectation.lean:137)

Subtracting a deterministic target from a coefficient inside an
expectation is legitimate because the normalized gap product has mean one.
Integrability of both terms is explicit.

```lean
lemma abs_integral_coefficient_mul_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F Y : Ω → ℝ} {B : ℝ}
    (hFY : Integrable (fun x => F x * Y x) μ) (hY : Integrable Y μ)
    (hY0 : ∀ᵐ x ∂μ, 0 ≤ Y x) (hEY : (∫ x, Y x ∂μ) = 1) :
    |(∫ x, F x * Y x ∂μ) - B| ≤ ∫ x, |F x - B| * Y x ∂μ
```


## Luce/Section5GapLaw.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce
```

### exponential_scale_to_unit

lemma; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:17)

```lean
lemma exponential_scale_to_unit {r : ℝ} (hr : 0 < r) :
    (expMeasure r).map (fun t => r * t) = expMeasure 1
```

### identityNormalizedGaps

def; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:41)

Identity-order gaps, constructed by exposing the first arrival and
subtracting it from the surviving clocks. A coordinate formula below
identifies this with the paper's remaining-rate times actual gap.

```lean
def identityNormalizedGaps : {n : ℕ} → Weights n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, _ => Fin.elim0
  | _n + 1, w, c => Fin.cons (w.total Finset.univ * c 0)
      (identityNormalizedGaps (w.removeFirst 0) (fun j => c j.succ - c 0))
```

### measurable_identityNormalizedGaps

theorem; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:46)

```lean
theorem measurable_identityNormalizedGaps {n : ℕ} (w : Weights n) :
    Measurable (identityNormalizedGaps w)
```

### removeFirst_zero_total

lemma; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:59)

```lean
lemma removeFirst_zero_total {n : ℕ} (w : Weights (n + 1)) :
    w.rate 0 + (w.removeFirst 0).total Finset.univ = w.total Finset.univ
```

### first_gap_density

lemma; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:64)

```lean
lemma first_gap_density {n : ℕ} (w : Weights (n + 1)) (t : ℝ) :
    exponentialPDF (w.rate 0) t *
      ENNReal.ofReal (Real.exp (-((w.removeFirst 0).total Finset.univ * t))) =
    ENNReal.ofReal (w.rate 0 / w.total Finset.univ) *
      exponentialPDF (w.total Finset.univ) t
```

### exponentialRace_surviving_order_integral

theorem; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:84)

Memorylessness with an arbitrary measurable test of all residual
clocks, retaining the event specifying the rest of the elimination order.

```lean
theorem exponentialRace_surviving_order_integral {n : ℕ} (w : Weights n)
    {s : ℝ} (hs : 0 ≤ s) (H : (Fin n → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ c, if (∀ i, s < c i) ∧ StrictMono c then H (fun i => c i - s) else 0
      ∂exponentialRace w) =
    ENNReal.ofReal (Real.exp (-(w.total Finset.univ * s))) *
      ∫⁻ c, if StrictMono c then H c else 0 ∂exponentialRace w
```

### standardGapLaw

def; [source line 113](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:113)

Standard independent exponentials, including the unique empty vector.

```lean
def standardGapLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => expMeasure 1)
```

### instance at line 116

instance; [source line 116](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:116)

```lean
instance standardGapLaw_isProbability (n : ℕ) : IsProbabilityMeasure (standardGapLaw n) := by
  let _ := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  unfold standardGapLaw
  infer_instance
```

### standardGapLaw_cons_integral

lemma; [source line 121](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:121)

```lean
lemma standardGapLaw_cons_integral (n : ℕ)
    (H : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x, H x ∂standardGapLaw (n + 1)) =
      ∫⁻ t, ∫⁻ u, H (Fin.cons t u) ∂standardGapLaw n ∂expMeasure 1
```

### measurable_finCons

lemma; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:141)

```lean
lemma measurable_finCons {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {a : Ω → ℝ} {b : Ω → Fin n → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => (Fin.cons (a x) (b x) : Fin (n + 1) → ℝ))
```

### identityNormalizedGaps_order_recursion

theorem; [source line 150](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:150)

One step of the joint gap law. The first normalized gap has law Exp(1)
and factors from an arbitrary test of the full residual ordered gap vector.

```lean
theorem identityNormalizedGaps_order_recursion {n : ℕ} (w : Weights (n + 1))
    (H : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ c, if StrictMono c then H (identityNormalizedGaps w c) else 0
      ∂exponentialRace w) =
    ENNReal.ofReal (w.rate 0 / w.total Finset.univ) *
      ∫⁻ t, ∫⁻ u, if StrictMono u then
        H (Fin.cons t (identityNormalizedGaps (w.removeFirst 0) u)) else 0
        ∂exponentialRace (w.removeFirst 0) ∂expMeasure 1
```

### exponentialRace_identityNormalizedGaps_integral

theorem; [source line 218](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:218)

The entire normalized gap vector factors from the identity elimination
order. The test function is arbitrary and need not factor over coordinates.

```lean
theorem exponentialRace_identityNormalizedGaps_integral {n : ℕ} (w : Weights n)
    (H : (Fin n → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ c, if StrictMono c then H (identityNormalizedGaps w c) else 0
      ∂exponentialRace w) =
    ENNReal.ofReal (w.mass (Equiv.refl (Fin n))) * ∫⁻ u, H u ∂standardGapLaw n
```

### exponentialRace_identityNormalizedGaps

theorem; [source line 248](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:248)

Equality of finite measures, equivalent to every joint normalized gap
event having the independent Exp(1) probability times the order probability.

```lean
theorem exponentialRace_identityNormalizedGaps {n : ℕ} (w : Weights n) :
    ((exponentialRace w).restrict {c | StrictMono c}).map (identityNormalizedGaps w) =
      ENNReal.ofReal (w.mass (Equiv.refl (Fin n))) • standardGapLaw n
```

### orderedWeights

def; [source line 272](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:272)

Rates listed in a specified elimination order; no equality between
different label rates is imposed.

```lean
def orderedWeights {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n)) : Weights n where
  rate q := w.rate (σ q)
  positive q := w.positive (σ q)
```

### orderedNormalizedGaps

def; [source line 277](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:277)

The normalized gap vector on a specified elimination order.

```lean
def orderedNormalizedGaps {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n))
    (c : Fin n → ℝ) : Fin n → ℝ :=
  identityNormalizedGaps (orderedWeights w σ) (fun q => c (σ q))
```

### measurable_orderedNormalizedGaps

theorem; [source line 281](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:281)

```lean
theorem measurable_orderedNormalizedGaps {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) : Measurable (orderedNormalizedGaps w σ)
```

### exponentialRace_orderedNormalizedGaps_integral

theorem; [source line 286](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:286)

```lean
theorem exponentialRace_orderedNormalizedGaps_integral {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (H : (Fin n → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ c, if StrictMono (fun q => c (σ q)) then H (orderedNormalizedGaps w σ c) else 0
      ∂exponentialRace w) =
    ENNReal.ofReal (w.mass σ) * ∫⁻ u, H u ∂standardGapLaw n
```

### exponentialRace_orderedNormalizedGaps

theorem; [source line 311](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:311)

Source equation `eq:race-gap-representation`, as the full joint measure
identity on every elimination order. In particular, normalized gaps remain
mutually independent after the complete order has been specified.

```lean
theorem exponentialRace_orderedNormalizedGaps {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) :
    ((exponentialRace w).restrict {c | StrictMono (fun q => c (σ q))}).map
        (orderedNormalizedGaps w σ) =
      ENNReal.ofReal (w.mass σ) • standardGapLaw n
```

### raceNormalizedGaps

def; [source line 340](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:340)

The gap vector obtained from the actual sorted draw permutation.

```lean
def raceNormalizedGaps {n : ℕ} (w : Weights n) (c : Fin n → ℝ) : Fin n → ℝ :=
  orderedNormalizedGaps w (raceDraw c) c
```

### measurable_raceNormalizedGaps

theorem; [source line 343](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:343)

```lean
theorem measurable_raceNormalizedGaps {n : ℕ} (w : Weights n) :
    Measurable (raceNormalizedGaps w)
```

### exponentialRace_raceNormalizedGaps_restrict_order

theorem; [source line 351](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:351)

```lean
theorem exponentialRace_raceNormalizedGaps_restrict_order {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) :
    ((exponentialRace w).restrict {c | raceDraw c = σ}).map (raceNormalizedGaps w) =
      ENNReal.ofReal (w.mass σ) • standardGapLaw n
```

### orderedRemainingRate

def; [source line 379](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:379)

Remaining rate just before the clock at position q rings. Position q
is zero-based, so this is the paper's W_q and includes the q-th clock.

```lean
def orderedRemainingRate {n : ℕ} (w : Weights n) (σ : Equiv.Perm (Fin n))
    (q : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (q ≤ ·), w.rate (σ k)
```

### previousOrderedTime

def; [source line 384](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:384)

The clock immediately preceding position q, with the sentinel T₀=0.

```lean
def previousOrderedTime {n : ℕ} (c : Fin n → ℝ) (q : Fin n) : ℝ :=
  if h : q.val = 0 then 0 else c ⟨q.val - 1, by omega⟩
```

### identityGapDuration

def; [source line 388](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:388)

A gap between successive ordered clocks, including the initial gap.

```lean
def identityGapDuration {n : ℕ} (c : Fin n → ℝ) (q : Fin n) : ℝ :=
  c q - previousOrderedTime c q
```

### orderedRemainingRate_identity_zero

lemma; [source line 391](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:391)

```lean
lemma orderedRemainingRate_identity_zero {n : ℕ} (w : Weights (n + 1)) :
    orderedRemainingRate w (Equiv.refl _) 0 = w.total Finset.univ
```

### orderedRemainingRate_identity_succ

lemma; [source line 395](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:395)

```lean
lemma orderedRemainingRate_identity_succ {n : ℕ} (w : Weights (n + 1)) (q : Fin n) :
    orderedRemainingRate w (Equiv.refl _) q.succ =
      orderedRemainingRate (w.removeFirst 0) (Equiv.refl _) q
```

### identityGapDuration_succ

lemma; [source line 402](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:402)

```lean
lemma identityGapDuration_succ {n : ℕ} (c : Fin (n + 1) → ℝ) (q : Fin n) :
    identityGapDuration c q.succ =
      identityGapDuration (fun j => c j.succ - c 0) q
```

### identityNormalizedGaps_eq_rate_mul_gap

theorem; [source line 423](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:423)

The recursive random vector is exactly the remaining rate multiplied
by the actual consecutive-clock gap, not a separately assumed noise vector.

```lean
theorem identityNormalizedGaps_eq_rate_mul_gap {n : ℕ} (w : Weights n)
    (c : Fin n → ℝ) (q : Fin n) :
    identityNormalizedGaps w c q =
      orderedRemainingRate w (Equiv.refl _) q * identityGapDuration c q
```

### orderedNormalizedGaps_eq_rate_mul_gap

theorem; [source line 438](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:438)

Literal coordinate form of the paper's ξ_q = W_q(T_(q+1)−T_q), for
every specified elimination order, including q=0.

```lean
theorem orderedNormalizedGaps_eq_rate_mul_gap {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ℝ) (q : Fin n) :
    orderedNormalizedGaps w σ c q = orderedRemainingRate w σ q *
      (c (σ q) - previousOrderedTime (fun k => c (σ k)) q)
```

### orderedRemainingRate_pos

theorem; [source line 444](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:444)

```lean
theorem orderedRemainingRate_pos {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) : 0 < orderedRemainingRate w σ q
```

### ordered_gap_eq_normalized_div_rate

theorem; [source line 450](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:450)

The literal gap representation has a strictly positive denominator.

```lean
theorem ordered_gap_eq_normalized_div_rate {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ℝ) (q : Fin n) :
    c (σ q) - previousOrderedTime (fun k => c (σ k)) q =
      orderedNormalizedGaps w σ c q / orderedRemainingRate w σ q
```

### orderedRemainingRate_eq_surviving_sum

theorem; [source line 459](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:459)

On the actual ordered positive clocks, the suffix rate is exactly the
total rate surviving strictly after the preceding arrival.

```lean
theorem orderedRemainingRate_eq_surviving_sum {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ℝ)
    (horder : StrictMono (fun k => c (σ k))) (hpos : ∀ i, 0 < c i) (q : Fin n) :
    orderedRemainingRate w σ q =
      ∑ i, if previousOrderedTime (fun k => c (σ k)) q < c i then w.rate i else 0
```

### exponentialRace_raceNormalizedGaps_integral

theorem; [source line 481](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:481)

Summing all elimination orders removes the conditioning without
changing the product law of normalized gaps.

```lean
theorem exponentialRace_raceNormalizedGaps_integral {n : ℕ} (w : Weights n)
    (H : (Fin n → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ c, H (raceNormalizedGaps w c) ∂exponentialRace w) =
      ∫⁻ u, H u ∂standardGapLaw n
```

### exponentialRace_raceNormalizedGaps

theorem; [source line 522](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:522)

```lean
theorem exponentialRace_raceNormalizedGaps {n : ℕ} (w : Weights n) :
    (exponentialRace w).map (raceNormalizedGaps w) = standardGapLaw n
```

### measurePreserving_raceNormalizedGaps

theorem; [source line 538](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:538)

```lean
theorem measurePreserving_raceNormalizedGaps {n : ℕ} (w : Weights n) :
    MeasurePreserving (raceNormalizedGaps w) (exponentialRace w) (standardGapLaw n)
```

### standardGapLaw_select

theorem; [source line 544](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:544)

Any deterministic collection of distinct normalized gap coordinates
has the corresponding product exponential law.

```lean
theorem standardGapLaw_select {n r : ℕ} (q : Fin r ↪ Fin n) :
    MeasurePreserving (fun u : Fin n → ℝ => fun a => u (q a))
      (standardGapLaw n) (standardGapLaw r)
```

### measurePreserving_selectedNormalizedGaps

theorem; [source line 559](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapLaw.lean:559)

```lean
theorem measurePreserving_selectedNormalizedGaps {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) :
    MeasurePreserving (fun c => fun a => raceNormalizedGaps w c (q a))
      (exponentialRace w) (standardGapLaw r)
```


## Luce/Section5GapMoments.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMoments.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace Luce
```

### exponential_one_density_pow

lemma; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMoments.lean:20)

```lean
private lemma exponential_one_density_pow (p : ℕ) :
    (fun x : ℝ => (exponentialPDF 1 x).toReal * x ^ p) =
      (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x) * x ^ p)
```

### integrable_pow_expMeasure_one

theorem; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMoments.lean:31)

Every natural moment is integrable under the rate-one exponential law.
No totalized integral is used to infer integrability.

```lean
theorem integrable_pow_expMeasure_one (p : ℕ) :
    Integrable (fun x : ℝ => x ^ p) (expMeasure 1)
```

### integral_pow_expMeasure_one

theorem; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMoments.lean:45)

The exact natural moment, including the zeroth moment.

```lean
theorem integral_pow_expMeasure_one (p : ℕ) :
    (∫ x : ℝ, x ^ p ∂expMeasure 1) = (p.factorial : ℝ)
```

### integrable_mixed_expMeasure_one

theorem; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMoments.lean:62)

Independent unit-exponential coordinates have all mixed moments.
The finite index type can be empty, and powers can be zero.

```lean
theorem integrable_mixed_expMeasure_one {ι : Type*} [Fintype ι] (p : ι → ℕ) :
    Integrable (fun x : ι → ℝ => ∏ i, x i ^ p i)
      (Measure.pi fun _ : ι => expMeasure 1)
```

### integral_mixed_expMeasure_one

theorem; [source line 70](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMoments.lean:70)

Exact joint mixed moment; distinct gaps are represented by distinct
coordinates of the product law, with no asserted independence of raw gaps.

```lean
theorem integral_mixed_expMeasure_one {ι : Type*} [Fintype ι] (p : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, x i ^ p i ∂Measure.pi (fun _ : ι => expMeasure 1)) =
      ∏ i, ((p i).factorial : ℝ)
```

### coordinate_mul_prod_eq_mixed

lemma; [source line 77](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMoments.lean:77)

```lean
private lemma coordinate_mul_prod_eq_mixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (x : ι → ℝ) :
    x i * ∏ j, x j = ∏ j, x j ^ (if j = i then 2 else 1)
```

### integrable_sum_mul_prod_expMeasure_one

theorem; [source line 94](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMoments.lean:94)

Integrability of the exact multigap Taylor envelope.

```lean
theorem integrable_sum_mul_prod_expMeasure_one {ι : Type*} [Fintype ι] :
    Integrable (fun x : ι → ℝ => (∑ i, x i) * ∏ i, x i)
      (Measure.pi fun _ : ι => expMeasure 1)
```

### integral_sum_mul_prod_expMeasure_one

theorem; [source line 103](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMoments.lean:103)

The Taylor envelope has expectation twice the number of selected gaps.
This explicitly accounts for the squared coordinate in every summand.

```lean
theorem integral_sum_mul_prod_expMeasure_one {ι : Type*} [Fintype ι] :
    (∫ x : ι → ℝ, (∑ i, x i) * ∏ i, x i ∂Measure.pi (fun _ : ι => expMeasure 1)) =
      2 * (Fintype.card ι : ℝ)
```


## Luce/Section5GapMomentTransfer.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMomentTransfer.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Luce
```

### integrable_selectedNormalizedGaps

theorem; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMomentTransfer.lean:18)

```lean
theorem integrable_selectedNormalizedGaps {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) (H : (Fin r → ℝ) → ℝ)
    (hH : Integrable H (standardGapLaw r)) :
    Integrable (fun c => H (fun a => raceNormalizedGaps w c (q a))) (exponentialRace w)
```

### integral_selectedNormalizedGaps

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMomentTransfer.lean:24)

```lean
theorem integral_selectedNormalizedGaps {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) (H : (Fin r → ℝ) → ℝ)
    (hH : Integrable H (standardGapLaw r)) :
    (∫ c, H (fun a => raceNormalizedGaps w c (q a)) ∂exponentialRace w) =
      ∫ u, H u ∂standardGapLaw r
```

### integrable_selectedNormalizedGaps_mixed

theorem; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMomentTransfer.lean:38)

All mixed natural moments of distinct actual normalized gaps are
integrable, with no rate bound and no assumption of gap independence.

```lean
theorem integrable_selectedNormalizedGaps_mixed {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) (p : Fin r → ℕ) :
    Integrable (fun c => ∏ a, raceNormalizedGaps w c (q a) ^ p a) (exponentialRace w)
```

### integral_selectedNormalizedGaps_mixed

theorem; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMomentTransfer.lean:45)

The exact mixed moment is the product of factorials. This includes
zero powers and the empty selection.

```lean
theorem integral_selectedNormalizedGaps_mixed {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) (p : Fin r → ℕ) :
    (∫ c, ∏ a, raceNormalizedGaps w c (q a) ^ p a ∂exponentialRace w) =
      ∏ a, ((p a).factorial : ℝ)
```

### integrable_selectedNormalizedGaps_taylorEnvelope

theorem; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMomentTransfer.lean:52)

```lean
theorem integrable_selectedNormalizedGaps_taylorEnvelope {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) :
    Integrable (fun c => (∑ a, raceNormalizedGaps w c (q a)) *
      ∏ a, raceNormalizedGaps w c (q a)) (exponentialRace w)
```

### integral_selectedNormalizedGaps_taylorEnvelope

theorem; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapMomentTransfer.lean:60)

The multigap Taylor envelope for the actual race has expectation 2r,
uniformly over every positive weight array and all distinct chosen gaps.

```lean
theorem integral_selectedNormalizedGaps_taylorEnvelope {n r : ℕ} (w : Weights n)
    (q : Fin r ↪ Fin n) :
    (∫ c, (∑ a, raceNormalizedGaps w c (q a)) *
      ∏ a, raceNormalizedGaps w c (q a) ∂exponentialRace w) = 2 * (r : ℝ)
```


## Luce/Section5GapProductExpectation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapProductExpectation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### abs_prod_le_uniform

lemma; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapProductExpectation.lean:19)

```lean
lemma abs_prod_le_uniform {r : ℕ} {A : Fin r → ℝ} {C : ℝ}
    (hA : ∀ a, |A a| ≤ C) : |∏ a, A a| ≤ C ^ r
```

### product_error_modulus

lemma; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapProductExpectation.lean:26)

A concrete modulus for finite products, valid at C=0 and r=0.

```lean
lemma product_error_modulus {r : ℕ} {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    {A B : Fin r → ℝ} (hA : ∀ a, |A a| ≤ C) (hB : ∀ a, |B a| ≤ C)
    (hAB : ∀ a, |A a - B a| < ε / (((r : ℝ) + 1) * (C + 1) ^ r)) :
    |(∏ a, A a) - ∏ a, B a| < ε
```

### uniform_product_error_probability

theorem; [source line 49](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapProductExpectation.lean:49)

Uniform convergence of scalar coefficients in probability gives
uniform convergence of their product in probability. The target values
may vary with both the row and the marked configuration.

```lean
theorem uniform_product_error_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    {ι : ℕ → Type*} {r : ℕ}
    (A : (n : ℕ) → ι n → Ω n → Fin r → ℝ)
    (B : (n : ℕ) → ι n → Fin r → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ i, ∀ᵐ x ∂μ n,
      (∀ a, |A n i x a| ≤ C) ∧ (∀ a, |B n i a| ≤ C))
    (hprob : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ i,
        (μ n).real {x | ∃ a, δ ≤ |A n i x a - B n i a|} < η) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ i,
        (μ n).real {x | ε ≤ |(∏ a, A n i x a) - ∏ a, B n i a|} < η
```


## Luce/Section5GapReservoir.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapReservoir.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped BigOperators Topology
namespace Luce
```

### deletedPrefixLabels

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapReservoir.lean:20)

Deleted labels together with the q labels preceding a compact rank.

```lean
def deletedPrefixLabels {n : ℕ} (removed : Finset (Fin n))
    (σ : Equiv.Perm (Fin (Finset.univ \ removed).card))
    (q : Fin (Finset.univ \ removed).card) : Finset (Fin n) :=
  removed ∪ (Finset.Iio q).image (fun k => deletedClockLabel removed (σ k))
```

### deletedPrefixLabels_card_le

lemma; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapReservoir.lean:25)

```lean
lemma deletedPrefixLabels_card_le {n : ℕ} (removed : Finset (Fin n))
    (σ : Equiv.Perm (Fin (Finset.univ \ removed).card))
    (q : Fin (Finset.univ \ removed).card) :
    (deletedPrefixLabels removed σ q).card ≤ removed.card + q.val
```

### total_compl_deletedPrefixLabels

theorem; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapReservoir.lean:37)

Complementing the deleted prefix leaves exactly the ordered suffix,
with each original unmarked label counted once.

```lean
theorem total_compl_deletedPrefixLabels {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (σ : Equiv.Perm (Fin (Finset.univ \ removed).card))
    (q : Fin (Finset.univ \ removed).card) :
    (∑ i ∈ Finset.univ \ deletedPrefixLabels removed σ q, w.rate i) =
      orderedRemainingRate (compactDeletedWeights w removed) σ q
```

### ProfileLimit.deleted_suffix_rate_uniform_lower

theorem; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapReservoir.lean:66)

Every compact elimination order has the same deterministic bulk lower
bound. The constant depends only on the fixed profile and α, not the marked
labels, their rates, q, the elimination order, or the row once it is large.

```lean
theorem ProfileLimit.deleted_suffix_rate_uniform_lower {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop,
      ∀ removed : Finset (Fin n), removed.card ≤ r →
        ∀ q : Fin (Finset.univ \ removed).card, (q.val : ℝ) ≤ α * n →
          ∀ σ : Equiv.Perm (Fin (Finset.univ \ removed).card),
            b * n ≤ orderedRemainingRate (compactDeletedWeights (w n) removed) σ q
```


## Luce/Section5GapTaylor.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace Luce
```

### exponentialGapMass

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:22)

Probability mass of a finite gap starting at `s` with length `h`.
The equality with the actual exponential measure is proved below.

```lean
def exponentialGapMass (a s h : ℝ) : ℝ :=
  survivalKernel s a - survivalKernel (s + h) a
```

### exponentialGapMass_nonneg

lemma; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:25)

```lean
lemma exponentialGapMass_nonneg {a s h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) :
    0 ≤ exponentialGapMass a s h
```

### exponentialGapMass_le

lemma; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:29)

```lean
lemma exponentialGapMass_le {a s h : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    exponentialGapMass a s h ≤ a * h
```

### exponentialGapMass_eq_measure

lemma; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:41)

```lean
lemma exponentialGapMass_eq_measure {a s h : ℝ}
    (ha : 0 < a) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    (expMeasure a).real (Ioo s (s + h)) = exponentialGapMass a s h
```

### exponentialGapMass_taylor

theorem; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:66)

A first-order expansion with a global quadratic bound, including `h=0`.
The harmless constant one (rather than one half) suffices for the source's
uniform mixed-moment argument.

```lean
theorem exponentialGapMass_taylor {a s h : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    |exponentialGapMass a s h - rateKernel s a * h| ≤ a ^ 2 * h ^ 2
```

### abs_prod_sub_prod_le_relative

theorem; [source line 106](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:106)

Telescoping with coordinate-dependent envelopes. In particular, zero
envelopes are allowed: no division by a gap or a rate is performed.

```lean
theorem abs_prod_sub_prod_le_relative {ι : Type*} (S : Finset ι)
    (u v z e : ι → ℝ)
    (hu : ∀ i ∈ S, |u i| ≤ z i) (hv : ∀ i ∈ S, |v i| ≤ z i)
    (hz : ∀ i ∈ S, 0 ≤ z i) (he : ∀ i ∈ S, 0 ≤ e i)
    (herr : ∀ i ∈ S, |u i - v i| ≤ e i * z i) :
    |(∏ i ∈ S, u i) - ∏ i ∈ S, v i| ≤ (∑ i ∈ S, e i) * ∏ i ∈ S, z i
```

### prod_exponentialGapMass_taylor

theorem; [source line 149](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:149)

The precise multigap error used in the source's mixed-moment step.
It retains all gap factors and remains true when any gap has length zero.

```lean
theorem prod_exponentialGapMass_taylor {ι : Type*} [Fintype ι]
    (a s h : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 ≤ s i) (hh : ∀ i, 0 ≤ h i) :
    |(∏ i, exponentialGapMass (a i) (s i) (h i)) -
      ∏ i, rateKernel (s i) (a i) * h i| ≤
      (∑ i, a i * h i) * ∏ i, a i * h i
```

### gap_abs_rateKernel_time_sub_le

theorem; [source line 168](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:168)

Uniform time variation of the marked density for a bounded marked rate.
This bound needs neither a positive lower bound on the rate nor bounded time.

```lean
theorem gap_abs_rateKernel_time_sub_le {a s t : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |rateKernel s a - rateKernel t a| ≤ a ^ 2 * |s - t|
```

### abs_gap_coefficient_sub_le

theorem; [source line 184](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:184)

The reciprocal denominator error is controlled by the actual common
positive reservoir lower bound. No upper bound on the remaining rate is used.

```lean
theorem abs_gap_coefficient_sub_le {a s t W D b : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hb : 0 < b) (hW : b ≤ W) (hD : b ≤ D) :
    |rateKernel s a / W - rateKernel t a / D| ≤
      a ^ 2 / b * |s - t| + a / b ^ 2 * |W - D|
```

### rescaled_prod_exponentialGapMass_taylor

theorem; [source line 217](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:217)

Explicit rescaled Taylor bound under the finite reservoir inequality.
Only this auxiliary estimate assumes a bound `M` on marked rates.

```lean
theorem rescaled_prod_exponentialGapMass_taylor {r : ℕ}
    (a s W ξ : Fin r → ℝ) {N b M : ℝ}
    (hN : 0 < N) (hb : 0 < b) (hM : 0 ≤ M)
    (ha : ∀ i, 0 ≤ a i) (haM : ∀ i, a i ≤ M)
    (hs : ∀ i, 0 ≤ s i) (hW : ∀ i, b * N ≤ W i) (hξ : ∀ i, 0 ≤ ξ i) :
    |N ^ r * (∏ i, exponentialGapMass (a i) (s i) (ξ i / W i)) -
      (∏ i, rateKernel (s i) (a i) / (W i / N)) * (∏ i, ξ i)| ≤
      (M / (b * N)) ^ (r + 1) * N ^ r * ((∑ i, ξ i) * ∏ i, ξ i)
```

### rescaled_gap_error_constant

lemma; [source line 265](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GapTaylor.lean:265)

The deterministic coefficient in the rescaled error is exactly O(1/N).
All divisions have proved positive denominators.

```lean
lemma rescaled_gap_error_constant {N b : ℝ} (hN : 0 < N) (hb : 0 < b)
    (M : ℝ) (r : ℕ) :
    (M / (b * N)) ^ (r + 1) * N ^ r = (M / b) ^ (r + 1) / N
```


## Luce/Section5GhostCylinder.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Luce
```

### clockBeforeCount_le_add_erase_self_of_eq_off

theorem; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:22)

A new clock is not before itself. Thus the upper change in its
before-count uses at most the other replaced labels. This sharp one-rank
saving is necessary for the lower endpoint of the paper's open window.

```lean
theorem clockBeforeCount_le_add_erase_self_of_eq_off {n : ℕ}
    (old new : Fin n → ℝ) (s : Finset (Fin n))
    (hsame : ∀ k, k ∉ s → new k = old k) (i : Fin n) :
    clockBeforeCount new (new i) ≤ clockBeforeCount old (new i) + (s.erase i).card
```

### MarkedRankCylinder

def; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:42)

The exact rank cylinder in the source, retaining its one-based ranks.

```lean
def MarkedRankCylinder {n ell : ℕ} (u j : Fin ell → Fin n)
    (clocks : Fin n → ℝ) : Prop :=
  ∀ a, raceRank clocks (u a) = (j a).val + 1
```

### GhostMarkedSuccess

def; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:48)

Simultaneous success of the independent replacement clocks in their
prescribed rank windows, all relative to one background.

```lean
def GhostMarkedSuccess {n ell : ℕ} (u j : Fin ell → Fin n)
    (c : Fin n → ℝ × ℝ) : Prop :=
  ∀ a, GhostCountWindow ell (fun i => (c i).1) (j a) (c (u a)).2
```

### measurableSet_markedRankCylinder

lemma; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:52)

```lean
lemma measurableSet_markedRankCylinder {n ell : ℕ} (u j : Fin ell → Fin n) :
    MeasurableSet {clocks | MarkedRankCylinder u j clocks}
```

### measurableSet_ghostMarkedSuccess

lemma; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:61)

```lean
lemma measurableSet_ghostMarkedSuccess {n ell : ℕ} (u j : Fin ell → Fin n) :
    MeasurableSet {c | GhostMarkedSuccess u j c}
```

### swapped_rankCylinder_implies_ghost

theorem; [source line 73](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:73)

Every prescribed new rank lies in the corresponding old ghost window.
The lower bound counts at most `ell-1` changed competitors; the upper bound
counts at most `ell`. No bound is assumed on the rates or spacings.

```lean
theorem swapped_rankCylinder_implies_ghost {n ell : ℕ}
    (u j : Fin ell → Fin n) (c : Fin n → ℝ × ℝ)
    (hpos : ∀ i, 0 < (swapClockCopies (Finset.univ.image u) c i).1)
    (hrank : MarkedRankCylinder u j
      (fun i => (swapClockCopies (Finset.univ.image u) c i).1)) :
    GhostMarkedSuccess u j c
```

### exponentialRace_positive_background

lemma; [source line 101](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:101)

```lean
lemma exponentialRace_positive_background {n : ℕ} (w : Weights n) :
    ∀ᵐ clocks ∂exponentialRace w, ∀ i, 0 < clocks i
```

### markedRankCylinder_probability_le_ghost

theorem; [source line 111](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:111)

Resampling the marked labels preserves the race law, and every
successful cylinder is contained in the ghost-window event.

```lean
theorem markedRankCylinder_probability_le_ghost {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} ≤
      pairedExponentialRace w {c | GhostMarkedSuccess u j c}
```

### ghostCountKernel_marked_product

theorem; [source line 128](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:128)

Conditional independence for arbitrary prescribed targets. Distinctness
is a condition on the sources only, as in the paper's cylinder probability.

```lean
theorem ghostCountKernel_marked_product {n ell : ℕ} (w : Weights n)
    (old : Fin n → ℝ) (u j : Fin ell → Fin n) (hu : Function.Injective u) :
    exponentialRace w {new | ∀ a, GhostCountWindow ell old (j a) (new (u a))} =
      ∏ a, ghostCountKernel w ell old (u a) (j a)
```

### lintegral_ghostCountKernel_marked_product

theorem; [source line 151](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:151)

Tonelli turns the conditional product into the probability of joint
success of the replacement clocks.

```lean
theorem lintegral_ghostCountKernel_marked_product {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) (hu : Function.Injective u) :
    (∫⁻ old, ∏ a, ghostCountKernel w ell old (u a) (j a) ∂exponentialRace w) =
      pairedExponentialRace w {c | GhostMarkedSuccess u j c}
```

### ghost_cylinder_bound_ennreal

theorem; [source line 177](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:177)

Equation `eq:ghost-cylinder-bound` with the paper's actual time-window
probabilities, in nonnegative integral form.

```lean
theorem ghost_cylinder_bound_ennreal {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) (hu : Function.Injective u) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} ≤
      ∫⁻ old, ∏ a, ghostOrderKernel w ell old (u a) (j a) ∂exponentialRace w
```

### aemeasurable_ghostCylinderProduct

lemma; [source line 193](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:193)

The cylinder product is measurable almost everywhere and is bounded
by one; no infinite or undefined real expectation is used.

```lean
lemma aemeasurable_ghostCylinderProduct {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) :
    AEMeasurable (fun old => ∏ a, ghostOrderKernel w ell old (u a) (j a))
      (exponentialRace w)
```

### ghostCylinderProduct_le_one

lemma; [source line 199](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:199)

```lean
lemma ghostCylinderProduct_le_one {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) (old : Fin n → ℝ) :
    (∏ a, ghostOrderKernel w ell old (u a) (j a)) ≤ 1
```

### lintegral_ghostCylinderProduct_le_one

lemma; [source line 204](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:204)

```lean
lemma lintegral_ghostCylinderProduct_le_one {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) :
    (∫⁻ old, ∏ a, ghostOrderKernel w ell old (u a) (j a) ∂exponentialRace w) ≤ 1
```

### ghost_cylinder_product_integrable

theorem; [source line 212](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:212)

```lean
theorem ghost_cylinder_product_integrable {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) :
    Integrable (fun old => ∏ a, ghostEntry w ell old (u a) (j a))
      (exponentialRace w)
```

### ghost_cylinder_bound

theorem; [source line 225](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostCylinder.lean:225)

Equation `eq:ghost-cylinder-bound`, as the real probability and real
expectation stated in the manuscript. The `ell` sources are distinct; no
restriction on the prescribed target ranks has been added.

```lean
theorem ghost_cylinder_bound {n ell : ℕ} (w : Weights n)
    (u j : Fin ell → Fin n) (hu : Function.Injective u) :
    (exponentialRace w).real {clocks | ∀ a, raceRank clocks (u a) = (j a).val + 1} ≤
      ∫ old, ∏ a, ghostEntry w ell old (u a) (j a) ∂exponentialRace w
```


## Luce/Section5GhostTimeSplit.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostTimeSplit.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Luce
```

### earlyGhostEntry

def; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostTimeSplit.lean:10)

Literal early part of the existing order-statistic ghost window.

```lean
def earlyGhostEntry {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i v : Fin n) (s : ℝ) : ℝ :=
  (expMeasure (w.rate i)).real
    ({t | GhostWindowByOrder old hinj ell v t} ∩ Set.Iic s)
```

### lateGhostEntry

def; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostTimeSplit.lean:16)

Literal complementary late part; the cutoff point belongs to the early part.

```lean
def lateGhostEntry {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i v : Fin n) (s : ℝ) : ℝ :=
  (expMeasure (w.rate i)).real
    ({t | GhostWindowByOrder old hinj ell v t} \ Set.Iic s)
```

### ghostEntry_eq_early_add_late

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostTimeSplit.lean:21)

```lean
theorem ghostEntry_eq_early_add_late {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i v : Fin n) (s : ℝ) :
    ghostEntry w ell old i v =
      earlyGhostEntry w ell old hinj i v s + lateGhostEntry w ell old hinj i v s
```

### earlyGhostEntry_le

theorem; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostTimeSplit.lean:31)

```lean
theorem earlyGhostEntry_le {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i v : Fin n) (s : ℝ) :
    earlyGhostEntry w ell old hinj i v s ≤ ghostEntry w ell old i v
```

### earlyGhostEntry_eq_zero_off_event

theorem; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostTimeSplit.lean:40)

```lean
theorem earlyGhostEntry_eq_zero_off_event {n j : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (i v : Fin n) (hv : v ∈ terminalShell n j)
    (hshell : (terminalShell n j).Nonempty) (s : ℝ)
    (hnot : old ∉ earlyGhostSurvivorEvent n (shellMax n j hshell) ell s) :
    earlyGhostEntry w ell old hinj i v s = 0
```

### early_ghost_return_le_event_indicator

theorem; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section5GhostTimeSplit.lean:55)

Pointwise domination by the full return contribution on the early
survivor event. This is a bound, not a redefinition of the actual edge.

```lean
theorem early_ghost_return_le_event_indicator {n j : ℕ} (w : Weights n) (k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (hshell : (terminalShell n j).Nonempty) (s : ℝ) :
    (∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostEntry w (k+2) old hinj u v s *
        markedReturnWeight (ghostEntry w (k+2) old) k v u) ≤
    (earlyGhostSurvivorEvent n (shellMax n j hshell) (k+2) s).indicator
      (fun old => ∑ v ∈ terminalShell n j, ∑ u : Fin n,
        ghostEntry w (k+2) old u v *
          markedReturnWeight (ghostEntry w (k+2) old) k v u) old
```


## Luce/Section5HighRates.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5HighRates.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace Luce
```

### high_rate_density_bound

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5HighRates.lean:21)

The pointwise density comparison in (1191–1197), before integration.

```lean
theorem high_rate_density_bound {n : ℕ} (w : Weights n) (M : ℝ)
    (hmass : (n : ℝ) / 2 ≤ ∑ k ∈ Finset.univ.filter (fun k => w.rate k ≤ M), w.rate k)
    (i : Fin n) (hi : M < w.rate i) {t : ℝ} (ht : 0 ≤ t) :
    w.rate i * Real.exp (-(w.rate i * t)) ≤
      (2 * w.rate i / n) * ∑ k, w.rate k * Real.exp (-(w.rate k * t))
```

### high_rate_ghostEntry_bound

theorem; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section5HighRates.lean:54)

Integrating the actual densities over J_j proves the column domination.
The zero extension at a tied background is handled explicitly.

```lean
theorem high_rate_ghostEntry_bound {n : ℕ} (w : Weights n) (ell : ℕ) (M : ℝ)
    (hmass : (n : ℝ) / 2 ≤ ∑ k ∈ Finset.univ.filter (fun k => w.rate k ≤ M), w.rate k)
    (old : Fin n → ℝ) (hnonneg : ∀ k, 0 ≤ old k)
    (i j : Fin n) (hi : M < w.rate i) :
    ghostEntry w ell old i j ≤ (2 * w.rate i / n) * ∑ k, ghostEntry w ell old k j
```

### highRateMass

def; [source line 71](D:/princeton/Research/Lean/Lean_luce/Luce/Section5HighRates.lean:71)

High-rate mass, with the strict cutoff used in Proposition 5.4.

```lean
def highRateMass (w : WeightArray) (n : ℕ) (M : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => M < (w n).rate i), (w n).rate i) / n
```

### highRateMass_eq_integral

lemma; [source line 74](D:/princeton/Research/Lean/Lean_luce/Luce/Section5HighRates.lean:74)

```lean
lemma highRateMass_eq_integral (w : WeightArray) (n : ℕ) (M : ℝ) :
    highRateMass w n M =
      ∫ x, (if M < stepProfile w n x then stepProfile w n x else 0) ∂profileMeasure
```

### integrable_highProfile

lemma; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section5HighRates.lean:80)

```lean
lemma integrable_highProfile (w : WeightArray) (n : ℕ) (M : ℝ) :
    Integrable (fun x => if M < stepProfile w n x then stepProfile w n x else 0)
      profileMeasure
```

### ProfileLimit.positivePart_tail

lemma; [source line 94](D:/princeton/Research/Lean/Lean_luce/Luce/Section5HighRates.lean:94)

An integrable profile has a vanishing positive-part tail. Positivity is
not needed in this auxiliary analytic lemma.

```lean
lemma ProfileLimit.positivePart_tail {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) :
    Tendsto (fun K : ℕ => ∫ x, max (f x - K) 0 ∂profileMeasure) atTop (𝓝 0)
```

### ProfileLimit.highRateMass_small

theorem; [source line 118](D:/princeton/Research/Lean/Lean_luce/Luce/Section5HighRates.lean:118)

The high-rate assertion of (1174–1178), with both cutoffs and the order
of quantifiers explicit. No uniform-integrability hypothesis is assumed.

```lean
theorem ProfileLimit.highRateMass_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∀ᶠ n in atTop, highRateMass w n M < ε
```

### ProfileLimit.eventually_moderate_half_mass

theorem; [source line 152](D:/princeton/Research/Lean/Lean_luce/Luce/Section5HighRates.lean:152)

The finite half-mass condition used above follows eventually from the
paper's assumptions. One cutoff threshold works for every larger M.

```lean
theorem ProfileLimit.eventually_moderate_half_mass {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / 2 ≤ ∑ k ∈ Finset.univ.filter (fun k => (w n).rate k ≤ M),
        (w n).rate k
```


## Luce/Section5Insertion.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open scoped BigOperators
namespace Luce
```

### clockBeforeCount

def; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:26)

The number of background clocks strictly below a proposed insertion time.

```lean
def clockBeforeCount {n : ℕ} (clocks : Fin n → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun i => clocks i < t).card
```

### clockBeforeCount_le_add_of_eq_off

theorem; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:32)

Changing only the labels in `s` changes any threshold count by at most
`s.card`; this is the rank perturbation used in `eq:approximate-permutation-path`.
Neither distinctness nor positivity is needed for the threshold-count assertion.

```lean
theorem clockBeforeCount_le_add_of_eq_off {n : ℕ}
    (old new : Fin n → ℝ) (s : Finset (Fin n))
    (hsame : ∀ i, i ∉ s → new i = old i) (t : ℝ) :
    clockBeforeCount new t ≤ clockBeforeCount old t + s.card
```

### clockBeforeCount_dist_le_of_eq_off

theorem; [source line 49](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:49)

The symmetric threshold-count form of the manuscript's finite-swap
rank perturbation.

```lean
theorem clockBeforeCount_dist_le_of_eq_off {n : ℕ}
    (old new : Fin n → ℝ) (s : Finset (Fin n))
    (hsame : ∀ i, i ∉ s → new i = old i) (t : ℝ) :
    Nat.dist (clockBeforeCount new t) (clockBeforeCount old t) ≤ s.card
```

### clockBeforeCount_mono

lemma; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:59)

```lean
lemma clockBeforeCount_mono {n : ℕ} (clocks : Fin n → ℝ) :
    Monotone (clockBeforeCount clocks)
```

### clockBeforeCount_le

lemma; [source line 67](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:67)

```lean
lemma clockBeforeCount_le {n : ℕ} (clocks : Fin n → ℝ) (t : ℝ) :
    clockBeforeCount clocks t ≤ n
```

### clockBeforeCount_arrivalTime

lemma; [source line 71](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:71)

```lean
lemma clockBeforeCount_arrivalTime {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (k : Fin n) :
    clockBeforeCount clocks (arrivalTime clocks hinj k) = k.val
```

### clockBeforeCount_lt_of_clock_lt

lemma; [source line 76](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:76)

```lean
lemma clockBeforeCount_lt_of_clock_lt {n : ℕ} (clocks : Fin n → ℝ)
    (i : Fin n) {t : ℝ} (ht : clocks i < t) :
    clockBeforeCount clocks (clocks i) < clockBeforeCount clocks t
```

### arrivalTime_lt_iff_clockBeforeCount

theorem; [source line 91](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:91)

Strict membership above an order statistic is exactly a lower bound on
the number of clocks before the proposed time.

```lean
theorem arrivalTime_lt_iff_clockBeforeCount {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (k : Fin n) (t : ℝ) :
    arrivalTime clocks hinj k < t ↔ k.val + 1 ≤ clockBeforeCount clocks t
```

### lt_arrivalTime_iff_clockBeforeCount

theorem; [source line 109](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:109)

Strict membership below an order statistic has the expected count
description whenever the proposed time is not a background clock.

```lean
theorem lt_arrivalTime_iff_clockBeforeCount {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (k : Fin n) (t : ℝ)
    (hne : t ≠ arrivalTime clocks hinj k) :
    t < arrivalTime clocks hinj k ↔ clockBeforeCount clocks t < k.val + 1
```

### GhostWindowByOrder

def; [source line 127](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:127)

The manuscript's open window with sentinel endpoints `T₀ = 0` and
`Tₙ₊₁ = ∞`. The upper sentinel is represented by a vacuous upper condition.

```lean
def GhostWindowByOrder {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (ell : ℕ) (j : Fin n) (t : ℝ) : Prop :=
  (if hlower : ell < j.val + 1 then
    arrivalTime clocks hinj ⟨j.val - ell, by omega⟩ < t
  else 0 < t) ∧
  (if hupper : j.val + 1 + ell ≤ n then
    t < arrivalTime clocks hinj ⟨j.val + ell, by omega⟩
  else True)
```

### ghostWindowByOrder_count_bounds

theorem; [source line 138](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:138)

Membership in a genuine open window implies the count inequalities
even when the proposed time coincides with a different background clock.

```lean
theorem ghostWindowByOrder_count_bounds {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (hnonneg : ∀ i, 0 ≤ clocks i)
    (ell : ℕ) (j : Fin n) (t : ℝ)
    (hwindow : GhostWindowByOrder clocks hinj ell j t) :
    0 < t ∧ j.val + 1 ≤ clockBeforeCount clocks t + ell ∧
      clockBeforeCount clocks t < j.val + 1 + ell
```

### ghostWindowByOrder_iff_count

theorem; [source line 173](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:173)

Exact correspondence between `eq:ghost-window` and the rank-count
window used for insertion.  Ties with the proposed time are excluded here;
independent continuous clocks discharge that condition almost surely.

```lean
theorem ghostWindowByOrder_iff_count {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (hnonneg : ∀ i, 0 ≤ clocks i)
    (ell : ℕ) (j : Fin n) (t : ℝ) (havoid : ∀ i, t ≠ clocks i) :
    GhostWindowByOrder clocks hinj ell j t ↔
      0 < t ∧ j.val + 1 ≤ clockBeforeCount clocks t + ell ∧
        clockBeforeCount clocks t < j.val + 1 + ell
```

### clockBeforeCount_window_dist

theorem; [source line 219](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:219)

Count-window membership costs at most `ell` ranks in zero-based
coordinates; hence the source's more generous `ell + 1` also holds.

```lean
theorem clockBeforeCount_window_dist {n : ℕ} (clocks : Fin n → ℝ)
    (ell : ℕ) (j : Fin n) (t : ℝ)
    (hlower : j.val + 1 ≤ clockBeforeCount clocks t + ell)
    (hupper : clockBeforeCount clocks t < j.val + 1 + ell) :
    Nat.dist (clockBeforeCount clocks t) j.val ≤ ell
```

### rankPermutation_dist_le_of_count_window

theorem; [source line 229](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:229)

The complete deterministic implication used after swapping replacement
clocks: old-window success gives approximate ranks in the new background.

```lean
theorem rankPermutation_dist_le_of_count_window {n : ℕ}
    (old new : Fin n → ℝ) (s : Finset (Fin n))
    (hsame : ∀ i, i ∉ s → new i = old i)
    (hinj : Function.Injective new) (ell : ℕ) (i j : Fin n)
    (hlower : j.val + 1 ≤ clockBeforeCount old (new i) + ell)
    (hupper : clockBeforeCount old (new i) < j.val + 1 + ell) :
    Nat.dist ((rankPermutation new hinj i).val) j.val ≤ ell + s.card
```

### ApproximatePermutationEdge

def; [source line 247](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:247)

Edges of the deterministic approximate rank graph, with labels and
positions both represented by `Fin n`.

```lean
def ApproximatePermutationEdge {n : ℕ} (σ : Equiv.Perm (Fin n)) (q : ℕ)
    (u v : Fin n) : Prop := Nat.dist (σ u).val v.val ≤ q
```

### approximatePermutationEdge_iff_oneBased

theorem; [source line 252](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:252)

The zero-based natural-distance convention is exactly the paper's
absolute difference of one-based ranks and labels.

```lean
theorem approximatePermutationEdge_iff_oneBased {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (q : ℕ) (u v : Fin n) :
    ApproximatePermutationEdge σ q u v ↔
      |((σ u).val : ℤ) + 1 - ((v.val : ℤ) + 1)| ≤ (q : ℤ)
```

### ApproximatePermutationPath

def; [source line 261](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:261)

A length-`m` path ending at `v`.  The tuple consists of precisely the
`m` source vertices; the endpoint is appended separately.

```lean
def ApproximatePermutationPath {n m : ℕ} (σ : Equiv.Perm (Fin n)) (q : ℕ)
    (v : Fin n) (u : Fin m → Fin n) : Prop :=
  ∀ a, ApproximatePermutationEdge σ q (u a)
    ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
```

### approximatePermutationPathCode

def; [source line 267](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:267)

Each approximate edge is encoded by one of `2*q+1` integer offsets.

```lean
def approximatePermutationPathCode {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (q : ℕ) (v : Fin n)
    (u : {u : Fin m → Fin n // ApproximatePermutationPath σ q v u}) :
    Fin m → Fin (2 * q + 1) := fun a =>
  ⟨(σ (u.val a)).val + q -
    ((Fin.snoc u.val v : Fin (m + 1) → Fin n) a.succ).val, by
    have h := u.property a
    dsimp [ApproximatePermutationEdge] at h
    unfold Nat.dist at h
    omega⟩
```

### approximatePermutationPathCode_injective

theorem; [source line 281](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:281)

For fixed endpoint, the sequence of offsets determines the path by
backward induction.  This checks the unique-preimage counting step in the
last paragraph of the proof of `lem:finite-insertion-path`.

```lean
theorem approximatePermutationPathCode_injective {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (q : ℕ) (v : Fin n) :
    Function.Injective (approximatePermutationPathCode (m := m) σ q v)
```

### approximatePermutationPath_count_le

theorem; [source line 309](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:309)

At most `(2*q+1)^m` directed approximate-permutation paths end at any
fixed vertex.  This is `fixed_points.tex`, lines 1131–1136.  Length zero
is included and has exactly one empty source tuple.

```lean
theorem approximatePermutationPath_count_le {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (q : ℕ) (v : Fin n) :
    (Finset.univ.filter (ApproximatePermutationPath (m := m) σ q v)).card ≤
      (2 * q + 1) ^ m
```

### distinct_approximatePermutationPath_count_le

theorem; [source line 321](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:321)

The genuine-cycle distinct-source condition only restricts the counted
paths, so dropping it is a proved overcounting step.

```lean
theorem distinct_approximatePermutationPath_count_le {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (q : ℕ) (v : Fin n) :
    (Finset.univ.filter fun u : Fin m → Fin n =>
      Function.Injective u ∧ ApproximatePermutationPath σ q v u).card ≤
      (2 * q + 1) ^ m
```

### countWindow_multiplicity_le

theorem; [source line 334](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:334)

A fixed time is contained in at most `2*ell+1` count windows.  This is
the deterministic multiplicity assertion preceding `eq:ghost-row-bound`;
it holds for any count and includes the clipped endpoint windows.

```lean
theorem countWindow_multiplicity_le (n ell c : ℕ) :
    (Finset.univ.filter fun j : Fin n =>
      j.val + 1 ≤ c + ell ∧ c < j.val + 1 + ell).card ≤ 2 * ell + 1
```

### ghostWindowByOrder_multiplicity_le

theorem; [source line 355](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Insertion.lean:355)

The same multiplicity bound for the manuscript's exact open windows,
using the proved order-statistic/count correspondence.

```lean
theorem ghostWindowByOrder_multiplicity_le {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (hnonneg : ∀ i, 0 ≤ clocks i)
    (ell : ℕ) (t : ℝ) :
    (Finset.univ.filter fun j : Fin n =>
      GhostWindowByOrder clocks hinj ell j t).card ≤ 2 * ell + 1
```


## Luce/Section5IntensityBounds.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityBounds.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce
```

### bulk_cycle_count_le_total

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityBounds.lean:9)

```lean
theorem bulk_cycle_count_le_total {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (α : ℝ) : Section5.bulkCycleCount R α k ≤ Section5.cycleCount R k
```

### bulk_cycle_count_mono

theorem; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityBounds.lean:14)

```lean
theorem bulk_cycle_count_mono {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) : Monotone (fun α => Section5.bulkCycleCount R α k)
```

### bulk_cycle_intensity_mono

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityBounds.lean:24)

```lean
theorem bulk_cycle_intensity_mono (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ) :
    MonotoneOn (fun α => bulkCycleTraceIntensity f α k) (Set.Iio 1)
```

### bulk_expectation_sub_le_tail

theorem; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityBounds.lean:41)

The difference of two bulk expectations is bounded by the original
endpoint expectation, without exchanging any limits or assuming moments.

```lean
theorem bulk_expectation_sub_le_tail (w : WeightArray) (k n : ℕ) (α β : ℝ) :
    (∫ z, (Section5.bulkCycleCount (raceRankPermutation z) β k : ℝ) ∂exponentialRace (w n)) -
    (∫ z, (Section5.bulkCycleCount (raceRankPermutation z) α k : ℝ) ∂exponentialRace (w n)) ≤
      cycleTailExpectation w k n α
```

### EndpointShellAssumption.bulk_intensity_tail_small

theorem; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityBounds.lean:60)

The manuscript's uniform Cauchy estimate for truncated intensities.
The cutoff is selected from the raw shell condition before beta and n.

```lean
theorem EndpointShellAssumption.bulk_intensity_tail_small
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, α < 1 ∧ ∀ β : ℝ, β < 1 →
      bulkCycleTraceIntensity f β k - bulkCycleTraceIntensity f α k ≤ ε
```

### EndpointShellAssumption.bulk_intensity_bounded

theorem; [source line 75](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityBounds.lean:75)

Uniform boundedness of the literal truncated intensities is a proved
consequence of the shell condition, not a finiteness input.

```lean
theorem EndpointShellAssumption.bulk_intensity_bounded
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ) :
    ∃ C : ℝ, ∀ α : ℝ, α < 1 → bulkCycleTraceIntensity f α k ≤ C
```


## Luce/Section5IntensityFinite.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace Luce
```

### cycleInteriorCutoff

def; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean:10)

```lean
def cycleInteriorCutoff (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ)+1)
```

### cycleInteriorCutoff_lt_one

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean:12)

```lean
theorem cycleInteriorCutoff_lt_one (n : ℕ) : cycleInteriorCutoff n < 1
```

### cycleInteriorCutoff_tendsto

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean:17)

```lean
theorem cycleInteriorCutoff_tendsto : Tendsto cycleInteriorCutoff atTop (𝓝 1)
```

### cyclic_cube_aecover

theorem; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean:22)

```lean
theorem cyclic_cube_aecover (r : ℕ) :
    AECover (cyclicProfileMeasure r) atTop
      (fun n => cyclicBulkCube r (cycleInteriorCutoff n))
```

### cyclicProfileMeasure_restrict_closed_bulk

theorem; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean:34)

```lean
theorem cyclicProfileMeasure_restrict_closed_bulk {r : ℕ} {α : ℝ} (hα : α < 1) :
    (cyclicProfileMeasure r).restrict (cyclicBulkCube r α) =
      volume.restrict (cyclicBulkCube r α)
```

### cycle_trace_nonneg_ae

theorem; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean:45)

```lean
theorem cycle_trace_nonneg_ae {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (k : ℕ) :
    ∀ᵐ x ∂cyclicProfileMeasure (k+1), 0 ≤ cycleTraceIntegrand f k x
```

### EndpointShellAssumption.cycle_trace_integrable

theorem; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean:60)

Full cyclic-density integrability follows from first moments and the
raw shell condition. No finite-intensity assumption is used.

```lean
theorem EndpointShellAssumption.cycle_trace_integrable
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ) :
    Integrable (cycleTraceIntegrand f k) (cyclicProfileMeasure (k+1))
```

### cycle_intensity_nonneg

theorem; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean:78)

```lean
theorem cycle_intensity_nonneg
    {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f) (k : ℕ) :
    0 ≤ cycleTraceIntensity f k
```

### cyclic_cube_aecover_left

theorem; [source line 83](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean:83)

```lean
theorem cyclic_cube_aecover_left (r : ℕ) :
    AECover (cyclicProfileMeasure r) (𝓝[<] (1 : ℝ)) (cyclicBulkCube r)
```

### EndpointShellAssumption.bulk_intensity_tendsto

theorem; [source line 98](D:/princeton/Research/Lean/Lean_luce/Luce/Section5IntensityFinite.lean:98)

Endpoint cutoff removal for the literal intensities, after proving
full integrability from the permitted inputs.

```lean
theorem EndpointShellAssumption.bulk_intensity_tendsto
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ) :
    Tendsto (fun α => bulkCycleTraceIntensity f α k) (𝓝[<] (1 : ℝ))
      (𝓝 (cycleTraceIntensity f k))
```


## Luce/Section5InteriorLowRates.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5InteriorLowRates.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set Function
open scoped BigOperators Topology
namespace Luce
```

### interiorLowCycleExpectation

def; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5InteriorLowRates.lean:11)

```lean
def interiorLowCycleExpectation (w : WeightArray) (L n : ℕ) (α δ : ℝ) : ℝ :=
  ∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L
    (Finset.univ.filter (fun v => (w n).rate v < δ ∧
      (v.val : ℝ)+1 ≤ α*n)) : ℝ) ∂exponentialRace (w n)
```

### interiorLowCycleExpectation_nonneg

theorem; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section5InteriorLowRates.lean:16)

```lean
theorem interiorLowCycleExpectation_nonneg (w : WeightArray) (L n : ℕ) (α δ : ℝ) :
    0 ≤ interiorLowCycleExpectation w L n α δ
```

### ProfileLimit.interiorLowCycleExpectation_bound

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5InteriorLowRates.lean:20)

```lean
theorem ProfileLimit.interiorLowCycleExpectation_bound {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (L : ℕ) (α : ℝ) (hα : α < 1) (M : ℝ) (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, ∀ᶠ n : ℕ in atTop,
      interiorLowCycleExpectation w L n α δ ≤
        (L : ℝ)*highCycleExpectation w L n M + K*lowRateDensity w n δ
```

### ProfileLimit.interiorLowCycleExpectation_small

theorem; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section5InteriorLowRates.lean:55)

```lean
theorem ProfileLimit.interiorLowCycleExpectation_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) (L : ℕ)
    (α : ℝ) (hα : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n : ℕ in atTop, interiorLowCycleExpectation w L n α δ < ε
```

### ProfileLimit.interior_low_rate_cycles_vanish

theorem; [source line 80](D:/princeton/Research/Lean/Lean_luce/Luce/Section5InteriorLowRates.lean:80)

```lean
theorem ProfileLimit.interior_low_rate_cycles_vanish {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (hnorm : NormalizedWeights w) (L : ℕ)
    (α : ℝ) (hα : α < 1) :
    Tendsto (fun δ : ℝ => limsup (fun n => interiorLowCycleExpectation w L n α δ) atTop)
      (𝓝[>] 0) (𝓝 0)
```


## Luce/Section5InteriorWindows.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5InteriorWindows.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### ProfileLimit.interior_ghostWindowLength

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5InteriorWindows.lean:21)

The literal O(1/n) expected-window estimate, with integrability and
eventual interior index validity proved from the profile reservoir.

```lean
theorem ProfileLimit.interior_ghostWindowLength {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (ell : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ j : Fin n,
      (j.val : ℝ) + 1 ≤ α * n →
        Integrable (fun old => ghostWindowLength ell old j) (exponentialRace (w n)) ∧
        (∫ old, ghostWindowLength ell old j ∂exponentialRace (w n)) ≤ K / n
```

### ProfileLimit.interior_ghostWindowLength_uniform

theorem; [source line 67](D:/princeton/Research/Lean/Lean_luce/Luce/Section5InteriorWindows.lean:67)

One constant and one eventual row threshold work for every window size
through L, preserving the source's K_L uniformity.

```lean
theorem ProfileLimit.interior_ghostWindowLength_uniform {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (L : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ ell : ℕ, ell ≤ L → ∀ j : Fin n,
      (j.val : ℝ) + 1 ≤ α * n →
        Integrable (fun old => ghostWindowLength ell old j) (exponentialRace (w n)) ∧
        (∫ old, ghostWindowLength ell old j ∂exponentialRace (w n)) ≤ K / n
```


## Luce/Section5LateCombined.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateCombined.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open scoped BigOperators
namespace Luce
```

### late_retained_pairs_bound

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateCombined.lean:12)

Combined late contribution for retained predecessors. The finite cover
premise is geometric and the floor thresholds are discharged by the raw
shell condition in the asymptotic application.

```lean
theorem late_retained_pairs_bound (w : WeightArray) (n J₀ J ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S S₀ : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ) (hJ₀ : 1 ≤ J₀) (hJ : 1 ≤ J)
    (hcut : 1 ≤ δ*((J : ℝ) - Real.sqrt J))
    (hrate : ∀ u ∈ S₀, δ ≤ (w n).rate u)
    (hcover : ∀ u ∈ S, u ∈ S₀ ∨ J₀ ≤ terminalShellNumber u)
    (hfloor : ∀ r ∈ Finset.Icc J₀ n, ∀ hs : (terminalShell n r).Nonempty,
      1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :
    (∑ v ∈ deepShellLabels n J, ∑ u ∈ S.filter (fun u => u < v),
      lateGhostEntry (w n) ell old hinj u v (terminalShellTime v) *
        markedReturnWeight (ghostEntry (w n) ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) *
        (Real.exp (-δ*((J : ℝ) - Real.sqrt J)) +
          ∑ r ∈ Finset.Icc J₀ n, if hs : (terminalShell n r).Nonempty then
            Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0)
```


## Luce/Section5LateCutoffLimits.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateCutoffLimits.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Filter
open scoped Topology
namespace Luce
```

### shellInteriorCutoff_lt_one

theorem; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateCutoffLimits.lean:8)

```lean
theorem shellInteriorCutoff_lt_one (J : ℕ) :
    1 - Real.exp (-(J : ℝ))/2 < 1
```

### eventually_exterior_shellNumber

theorem; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateCutoffLimits.lean:13)

The spatial interior cutoff is fixed before n. Integer rounding is
absorbed by the factor two already used in the Section 4 shell cover.

```lean
theorem eventually_exterior_shellNumber (J : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ v : Fin n,
      (1 - Real.exp (-(J : ℝ))/2)*(n : ℝ) < (v.val : ℝ)+1 →
        J ≤ terminalShellNumber v
```

### tendsto_shellBufferTime_atTop

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateCutoffLimits.lean:24)

```lean
theorem tendsto_shellBufferTime_atTop :
    Tendsto (fun J : ℕ => (J : ℝ) - Real.sqrt J) atTop atTop
```

### eventually_interior_density_cutoff

theorem; [source line 39](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateCutoffLimits.lean:39)

```lean
theorem eventually_interior_density_cutoff {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ J : ℕ in atTop, 1 ≤ δ*((J : ℝ) - Real.sqrt J)
```

### tendsto_interior_late_error

theorem; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateCutoffLimits.lean:46)

```lean
theorem tendsto_interior_late_error {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun J : ℕ => Real.exp (-δ*((J : ℝ) - Real.sqrt J))) atTop (𝓝 0)
```


## Luce/Section5LateDensity.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateDensity.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Luce
```

### ghost_subwindow_density

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateDensity.lean:9)

Density representation for any measurable part of the literal ghost window.

```lean
theorem ghost_subwindow_density {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (i v : Fin n) (T : Set ℝ) (hT : MeasurableSet T)
    (hsub : T ⊆ {t | GhostWindowByOrder old hinj ell v t}) :
    (expMeasure (w.rate i)).real T =
      ∫ t in T, w.rate i * Real.exp (-w.rate i * t)
```

### lateGhostEntry_eq_window_integral

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateDensity.lean:33)

```lean
theorem lateGhostEntry_eq_window_integral {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (i v : Fin n) (s : ℝ) :
    lateGhostEntry w ell old hinj i v s =
      ∫ t in Set.Ioi s, {t | GhostWindowByOrder old hinj ell v t}.indicator
        (fun t => w.rate i * Real.exp (-w.rate i*t)) t
```

### lateGhostEntry_antitone

theorem; [source line 51](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateDensity.lean:51)

```lean
theorem lateGhostEntry_antitone {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i v : Fin n) :
    Antitone (lateGhostEntry w ell old hinj i v)
```


## Luce/Section5LateKernel.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateKernel.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### lateGhostKernel

def; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateKernel.lean:11)

The complementary part of the original ghost probability.

```lean
def lateGhostKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (u v : Fin n) (s : ℝ) : ℝ :=
  ghostEntry w ell old u v - earlyGhostKernel w ell old u v s
```

### lateGhostKernel_eq_entry

theorem; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateKernel.lean:15)

```lean
theorem lateGhostKernel_eq_entry {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (u v : Fin n) (s : ℝ) :
    lateGhostKernel w ell old u v s = lateGhostEntry w ell old hinj u v s
```

### lateGhostKernel_nonneg

theorem; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateKernel.lean:22)

```lean
theorem lateGhostKernel_nonneg {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (u v : Fin n) (s : ℝ) :
    0 ≤ lateGhostKernel w ell old u v s
```

### integrable_late_return_product

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateKernel.lean:27)

```lean
theorem integrable_late_return_product {n : ℕ} (w : Weights n) (k : ℕ)
    (v u : Fin n) (s : ℝ) :
    Integrable (fun old => lateGhostKernel w (k+2) old u v s *
      markedReturnWeight (ghostEntry w (k+2) old) k v u) (exponentialRace w)
```

### late_retained_expectation_bound

theorem; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateKernel.lean:37)

The combined late bound for the actual canonical race, with the
background hypotheses discharged almost surely, not assumed.

```lean
theorem late_retained_expectation_bound (w : WeightArray) (n J₀ J k : ℕ)
    (S S₀ : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ) (hJ₀ : 1 ≤ J₀) (hJ : 1 ≤ J)
    (hcut : 1 ≤ δ*((J : ℝ) - Real.sqrt J))
    (hrate : ∀ u ∈ S₀, δ ≤ (w n).rate u)
    (hcover : ∀ u ∈ S, u ∈ S₀ ∨ J₀ ≤ terminalShellNumber u)
    (hfloor : ∀ r ∈ Finset.Icc J₀ n, ∀ hs : (terminalShell n r).Nonempty,
      1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :
    (∫ old, ∑ v ∈ deepShellLabels n J, ∑ u ∈ S.filter (fun u => u < v),
      lateGhostKernel (w n) (k+2) old u v (terminalShellTime v) *
        markedReturnWeight (ghostEntry (w n) (k+2) old) k v u
      ∂exponentialRace (w n)) ≤
      (2*(k+2)+1 : ℕ)^(k+2) *
        (Real.exp (-δ*((J : ℝ) - Real.sqrt J)) +
          ∑ r ∈ Finset.Icc J₀ n, if hs : (terminalShell n r).Nonempty then
            Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0)
```


## Luce/Section5LateMarkedIntegral.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateMarkedIntegral.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### late_marked_edge_integral

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateMarkedIntegral.lean:12)

Integrating the marked-edge bound over the source cutoff. Its local
rate and time premises are supplied by shell minima or retained interior rates.

```lean
theorem late_marked_edge_integral {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S : Finset (Fin n)) {b s : ℝ} (hb : 0 < b) (hbs : 1 ≤ b*s)
    (hrate : ∀ u ∈ S, b ≤ w.rate u) :
    (∫ t in Set.Ioi s,
      ∑ v ∈ Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t),
        ∑ u ∈ S, w.rate u * Real.exp (-w.rate u*t) *
          markedReturnWeight (ghostEntry w ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) * Real.exp (-b*s)
```

### late_source_shell_marked_integral

theorem; [source line 58](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateMarkedIntegral.lean:58)

```lean
theorem late_source_shell_marked_integral (w : WeightArray) (n r ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (hs : (terminalShell n r).Nonempty)
    (hfloor : 1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :
    (∫ t in Set.Ioi ((r : ℝ) - Real.sqrt r),
      ∑ v ∈ Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t),
        ∑ u ∈ terminalShell n r, (w n).rate u * Real.exp (-(w n).rate u*t) *
          markedReturnWeight (ghostEntry (w n) ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) *
        Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r))
```


## Luce/Section5LatePairBound.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LatePairBound.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open scoped BigOperators
namespace Luce
```

### late_ordered_pairs_le_common_cutoff

theorem; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LatePairBound.lean:10)

Move each target's late cutoff back to a common source cutoff while
the predecessor relation is still present. Only then enlarge the pair sum.

```lean
theorem late_ordered_pairs_le_common_cutoff {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old)
    (T S : Finset (Fin n)) (cut : Fin n → ℝ) (s : ℝ)
    (htime : ∀ v ∈ T, ∀ u ∈ S, u < v → s ≤ cut v) :
    (∑ v ∈ T, ∑ u ∈ S.filter (fun u => u < v),
      lateGhostEntry w ell old hinj u v (cut v) *
        markedReturnWeight (ghostEntry w ell old) k v u) ≤
    ∑ v : Fin n, ∑ u ∈ S, lateGhostEntry w ell old hinj u v s *
      markedReturnWeight (ghostEntry w ell old) k v u
```

### late_ordered_pairs_bound

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LatePairBound.lean:43)

```lean
theorem late_ordered_pairs_bound {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (T S : Finset (Fin n)) (cut : Fin n → ℝ) {b s : ℝ}
    (hb : 0 < b) (hbs : 1 ≤ b*s) (hrate : ∀ u ∈ S, b ≤ w.rate u)
    (htime : ∀ v ∈ T, ∀ u ∈ S, u < v → s ≤ cut v) :
    (∑ v ∈ T, ∑ u ∈ S.filter (fun u => u < v),
      lateGhostEntry w ell old hinj u v (cut v) *
        markedReturnWeight (ghostEntry w ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) * Real.exp (-b*s)
```


## Luce/Section5LateReturnSum.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateReturnSum.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### late_return_sum_eq_integral

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateReturnSum.lean:12)

Exact interchange of finite return sums with the literal late-edge
integral, at a common source cutoff. All integrability is proved.

```lean
theorem late_return_sum_eq_integral {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S : Finset (Fin n)) (s : ℝ) :
    (∑ v : Fin n, ∑ u ∈ S, lateGhostEntry w ell old hinj u v s *
      markedReturnWeight (ghostEntry w ell old) k v u) =
    ∫ t in Set.Ioi s,
      ∑ v ∈ Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t),
        ∑ u ∈ S, w.rate u * Real.exp (-w.rate u*t) *
          markedReturnWeight (ghostEntry w ell old) k v u
```

### late_return_sum_le

theorem; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateReturnSum.lean:46)

The concrete late ghost-return sum inherits the integrated marked-edge
bound. The source-set minimum and cutoff premises remain explicit helpers.

```lean
theorem late_return_sum_le {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S : Finset (Fin n)) {b s : ℝ} (hb : 0 < b) (hbs : 1 ≤ b*s)
    (hrate : ∀ u ∈ S, b ≤ w.rate u) :
    (∑ v : Fin n, ∑ u ∈ S, lateGhostEntry w ell old hinj u v s *
      markedReturnWeight (ghostEntry w ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) * Real.exp (-b*s)
```


## Luce/Section5LateShellGeometry.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateShellGeometry.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Filter
open scoped Topology ENNReal
namespace Luce
```

### shell_buffer_time_mono

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateShellGeometry.lean:9)

```lean
theorem shell_buffer_time_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x - Real.sqrt x ≤ y - Real.sqrt y
```

### predecessor_shell_index_le

theorem; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateShellGeometry.lean:23)

Keeping the marked predecessor below the root is essential for this
comparison; the logarithmic shells themselves need no regularity.

```lean
theorem predecessor_shell_index_le {n r j : ℕ} {u v : Fin n}
    (hu : u ∈ terminalShell n r) (hv : v ∈ terminalShell n j) (huv : u < v) : r ≤ j
```

### predecessor_shell_buffer_le

theorem; [source line 42](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateShellGeometry.lean:42)

```lean
theorem predecessor_shell_buffer_le {n r j : ℕ} {u v : Fin n}
    (hu : u ∈ terminalShell n r) (hv : v ∈ terminalShell n j) (huv : u < v) :
    (r : ℝ) - Real.sqrt r ≤ (j : ℝ) - Real.sqrt j
```

### EndpointShellAssumption.eventually_buffered_floor_gt_one

theorem; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateShellGeometry.lean:50)

The late-density monotonicity threshold is proved from the raw shell
assumption. It is eventual in n, with J chosen first, not a uniform rate floor.

```lean
theorem EndpointShellAssumption.eventually_buffered_floor_gt_one {w : WeightArray}
    (h : EndpointShellAssumption w) :
    ∃ J : ℕ, 2 ≤ J ∧ ∀ᶠ n in atTop, ∀ r : ℕ, J ≤ r →
      ∀ hs : (terminalShell n r).Nonempty,
        1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)
```


## Luce/Section5LateSourceBounds.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateSourceBounds.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open scoped BigOperators
namespace Luce
```

### deepShellLabels

def; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateSourceBounds.lean:9)

```lean
def deepShellLabels (n J : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => J ≤ terminalShellNumber v)
```

### late_terminal_source_bound

theorem; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateSourceBounds.lean:14)

Terminal predecessors are bounded using their own shell cutoff, after
the ordered-pair comparison has been proved for every target.

```lean
theorem late_terminal_source_bound (w : WeightArray) (n r J ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (hJ : 1 ≤ J) (hs : (terminalShell n r).Nonempty)
    (hfloor : 1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :
    (∑ v ∈ deepShellLabels n J, ∑ u ∈ (terminalShell n r).filter (fun u => u < v),
      lateGhostEntry (w n) ell old hinj u v (terminalShellTime v) *
        markedReturnWeight (ghostEntry (w n) ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) *
        Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r))
```

### late_interior_source_bound

theorem; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LateSourceBounds.lean:32)

Interior predecessors use their retained low-rate cutoff. There is no
endpoint assumption in this estimate.

```lean
theorem late_interior_source_bound {n : ℕ} (w : Weights n) (J ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ) (hJ : 1 ≤ J)
    (hcut : 1 ≤ δ*((J : ℝ) - Real.sqrt J)) (hrate : ∀ u ∈ S, δ ≤ w.rate u) :
    (∑ v ∈ deepShellLabels n J, ∑ u ∈ S.filter (fun u => u < v),
      lateGhostEntry w ell old hinj u v (terminalShellTime v) *
        markedReturnWeight (ghostEntry w ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) * Real.exp (-δ*((J : ℝ) - Real.sqrt J))
```


## Luce/Section5Lemma52.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Lemma52.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace Luce
```

### section5_bounded_marked_asymptotic

theorem; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Lemma52.lean:23)

Equation `eq:bounded-marked-asymptotic`, uniformly over arbitrary
distinct marked labels and distinct, macroscopically separated bulk ranks.

```lean
theorem section5_bounded_marked_asymptotic
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a, (w n).rate (i a) ≤ M) →
        (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
        (∀ a b, a ≠ b → ζ * n ≤ |((j a).val : ℝ) - (j b).val|) →
        |(n : ℝ) ^ r * (exponentialRace (w n)).real
            {old | ∀ a, raceRank old (i a) = (j a).val + 1} -
          ∏ a, finiteCyclicDensity (w n) f (i a) (j a)| < ε
```

### section5_cyclic_local

theorem; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Lemma52.lean:41)

Equation `eq:cyclic-local-limit` on the literal closed cube with
Lebesgue measure. The test may be signed and is only required continuous
on that cube. The statement includes every α<1, including α≤0.

```lean
theorem section5_cyclic_local
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) (hr : 0 < r)
    (α : ℝ) (hα : α < 1) (τ : Equiv.Perm (Fin r))
    (g : (Fin r → ℝ) → ℝ) (hg : ContinuousOn g (cyclicBulkCube r α)) :
    Tendsto (fun n => cyclicRaceSum (w n) α τ g) atTop
      (𝓝 (∫ x in cyclicBulkCube r α,
        g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a))))
```

### section5_lemma52

theorem; [source line 56](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Lemma52.lean:56)

The whole of Lemma 5.2: cyclic convergence and its uniform weighted
bulk cylinder bound, with all mathematical assumptions visible.

```lean
theorem section5_lemma52
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) (hr : 0 < r)
    (α : ℝ) (hα : α < 1) (τ : Equiv.Perm (Fin r))
    (g : (Fin r → ℝ) → ℝ) (hg : ContinuousOn g (cyclicBulkCube r α)) :
    Tendsto (fun n => cyclicRaceSum (w n) α τ g) atTop
      (𝓝 (∫ x in cyclicBulkCube r α,
        g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a)))) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
        ∀ i j : Fin r ↪ Fin n,
          (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
            (exponentialRace (w n)).real
              {old | ∀ a, raceRank old (i a) = (j a).val + 1} ≤
                K / (n : ℝ) ^ r * ∏ a, (w n).rate (i a)
```


## Luce/Section5LowCycleProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped BigOperators ENNReal Topology
namespace Luce
```

### boundedCycleEvent

def; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleProbability.lean:17)

```lean
def boundedCycleEvent {n : ℕ} (w : Weights n) (k : ℕ) (M : ℝ) (v : Fin n) :
    Set (Fin n → ℝ) :=
  {clocks | minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1 ∧
    OrbitAvoids (raceRankPermutation clocks)
      (Finset.univ.filter (fun i => M < w.rate i)) v}
```

### measurableSet_boundedCycleEvent

lemma; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleProbability.lean:23)

```lean
lemma measurableSet_boundedCycleEvent {n : ℕ} (w : Weights n) (k : ℕ)
    (M : ℝ) (v : Fin n) : MeasurableSet (boundedCycleEvent w k M v)
```

### exists_bounded_cycle_tail

lemma; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleProbability.lean:33)

The rooted tuple supplied by an actual cycle inherits exactly its
vertex restriction. No restriction on any other label is introduced.

```lean
lemma exists_bounded_cycle_tail {n k : ℕ} (w : Weights n) (R : Equiv.Perm (Fin n))
    (M : ℝ) (v : Fin n) (hp : minimalPeriod (R : Fin n → Fin n) v = k + 1)
    (ha : OrbitAvoids R (Finset.univ.filter (fun i => M < w.rate i)) v) :
    ∃ u : Fin k → Fin n, Injective u ∧ (∀ a, u a ≠ v) ∧
      (∀ a, w.rate ((Fin.cons v u : Fin (k + 1) → Fin n) a) ≤ M) ∧
      ∀ a, R ((Fin.cons v u : Fin (k + 1) → Fin n) a) =
        (Fin.snoc u v : Fin (k + 1) → Fin n) a
```

### bounded_cycle_probability_le_ghost

theorem; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleProbability.lean:61)

The restricted rooted-cylinder union bound, with every selected label
and its original exponential rate retained.

```lean
theorem bounded_cycle_probability_le_ghost {n : ℕ} (w : Weights n)
    (k : ℕ) (M : ℝ) (v : Fin n) :
    (exponentialRace w).real (boundedCycleEvent w k M v) ≤
      ∫ old, ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        Injective u ∧ (∀ a, u a ≠ v) ∧
          ∀ a, w.rate ((Fin.cons v u : Fin (k + 1) → Fin n) a) ≤ M),
        ∏ a : Fin (k + 1), ghostEntry w (k + 1) old
          ((Fin.cons v u : Fin (k + 1) → Fin n) a)
          ((Fin.snoc u v : Fin (k + 1) → Fin n) a) ∂exponentialRace w
```

### bounded_cycle_probability_le_window

theorem; [source line 114](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleProbability.lean:114)

Finite restricted cycle bound after integrating the deterministic row
estimate. Integrability of the actual length is an explicit auxiliary premise
and is discharged from the reservoir in the next theorem.

```lean
theorem bounded_cycle_probability_le_window {n : ℕ} (w : Weights n)
    (k : ℕ) (M : ℝ) (hM : 0 ≤ M) (v : Fin n) (hv : v.val + (k + 1) < n)
    (hi : Integrable (fun old => ghostWindowLength (k + 1) old v) (exponentialRace w)) :
    (exponentialRace w).real (boundedCycleEvent w k M v) ≤
      (M * (2 * (k + 1) + 1 : ℕ) ^ k) *
        ∫ old, ghostWindowLength (k + 1) old v ∂exponentialRace w
```

### ProfileLimit.bounded_cycle_probability_uniform

theorem; [source line 129](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleProbability.lean:129)

Source 1225–1230 with every auxiliary window premise discharged.

```lean
theorem ProfileLimit.bounded_cycle_probability_uniform {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (L : ℕ) (M : ℝ) (hM : 0 < M)
    {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ v : Fin n,
      (v.val : ℝ) + 1 ≤ α * n → ∀ k : Fin L,
        (exponentialRace (w n)).real (boundedCycleEvent (w n) k.val M v) ≤ K / n
```

### shortCycleVertexCountAvoiding_expectation_le

theorem; [source line 163](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleProbability.lean:163)

The restricted vertex count is a finite sum of the actual short-cycle
events. The positive period of a finite permutation supplies the length
index; the estimate does not omit fixed points.

```lean
theorem shortCycleVertexCountAvoiding_expectation_le {n : ℕ} (w : Weights n)
    (L : ℕ) (M : ℝ) (S : Finset (Fin n)) :
    (∫ clocks, (shortCycleVertexCountAvoiding (raceRankPermutation clocks) L S
      (Finset.univ.filter (fun i => M < w.rate i)) : ℝ) ∂exponentialRace w) ≤
      ∑ v ∈ S, ∑ k : Fin L, (exponentialRace w).real (boundedCycleEvent w k.val M v)
```


## Luce/Section5LowCycleRows.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleRows.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace Luce
```

### forwardPathWeight

def; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleRows.lean:19)

An open path starting at v, with its k successive targets exposed.

```lean
def forwardPathWeight {α : Type*} {k : ℕ} (p : α → α → ℝ)
    (v : α) (u : Fin k → α) : ℝ :=
  ∏ a, p ((Fin.cons v u : Fin (k + 1) → α) a.castSucc) (u a)
```

### forwardPathWeight_cons

lemma; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleRows.lean:23)

```lean
lemma forwardPathWeight_cons {α : Type*} {k : ℕ} (p : α → α → ℝ)
    (v x : α) (u : Fin k → α) :
    forwardPathWeight p v (Fin.cons x u) = p v x * forwardPathWeight p x u
```

### forwardPathWeight_sum_le

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleRows.lean:30)

Repeated targets are included in this upper bound. Nonnegativity
justifies subsequently dropping the distinctness and rate restrictions.

```lean
theorem forwardPathWeight_sum_le {α : Type*} [Fintype α]
    (p : α → α → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (C : ℝ) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, p i j ≤ C)
    (k : ℕ) (v : α) :
    (∑ u : Fin k → α, forwardPathWeight p v u) ≤ C ^ k
```

### ghostWindowVolume_ne_top_of_interior

lemma; [source line 52](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleRows.lean:52)

A nonterminal ghost window has finite volume. This is proved before
using its real length, so `toReal` cannot turn an infinite length into zero.

```lean
lemma ghostWindowVolume_ne_top_of_interior {n : ℕ} (ell : ℕ)
    (old : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ old i)
    (j : Fin n) (hj : j.val + ell < n) : ghostWindowVolume ell old j ≠ ⊤
```

### ghostEntry_le_rate_mul_length

theorem; [source line 68](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleRows.lean:68)

The closing-edge inequality in source 1225–1227, derived from the
literal density integral and finite length of J_j.

```lean
theorem ghostEntry_le_rate_mul_length {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ old i)
    (i j : Fin n) (hj : j.val + ell < n) :
    ghostEntry w ell old i j ≤ w.rate i * ghostWindowLength ell old j
```

### rootedGhostProduct_eq_forward

lemma; [source line 95](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleRows.lean:95)

Factoring the closing edge preserves the rooted tuple, including
the fixed-point case k=0.

```lean
lemma rootedGhostProduct_eq_forward {n k : ℕ} (w : Weights n)
    (ell : ℕ) (old : Fin n → ℝ) (v : Fin n) (u : Fin k → Fin n) :
    (∏ a : Fin (k + 1), ghostEntry w ell old
      ((Fin.cons v u : Fin (k + 1) → Fin n) a)
      ((Fin.snoc u v : Fin (k + 1) → Fin n) a)) =
    forwardPathWeight (ghostEntry w ell old) v u *
      ghostEntry w ell old ((Fin.cons v u : Fin (k + 1) → Fin n) (Fin.last k)) v
```

### bounded_ghost_cycle_sum_le

theorem; [source line 106](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowCycleRows.lean:106)

Deterministic row summation, source 1227–1230. The finite sum retains
the exact distinct rooted tuples with all their source rates at most M.

```lean
theorem bounded_ghost_cycle_sum_le {n : ℕ} (w : Weights n) (k : ℕ)
    (M : ℝ) (hM : 0 ≤ M) (old : Fin n → ℝ)
    (hnonneg : ∀ i, 0 ≤ old i) (v : Fin n) (hv : v.val + (k + 1) < n) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
      Injective u ∧ (∀ a, u a ≠ v) ∧
        ∀ a, w.rate ((Fin.cons v u : Fin (k + 1) → Fin n) a) ≤ M),
      ∏ a : Fin (k + 1), ghostEntry w (k + 1) old
        ((Fin.cons v u : Fin (k + 1) → Fin n) a)
        ((Fin.snoc u v : Fin (k + 1) → Fin n) a)) ≤
      (M * ghostWindowLength (k + 1) old v) * (2 * (k + 1) + 1 : ℕ) ^ k
```


## Luce/Section5LowRates.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowRates.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Luce
```

### lowRateDensity

def; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowRates.lean:19)

```lean
def lowRateDensity (w : WeightArray) (n : ℕ) (δ : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i : Fin n => (w n).rate i < δ)).card : ℝ) / n
```

### lowRateDensity_eq_integral

lemma; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowRates.lean:22)

```lean
lemma lowRateDensity_eq_integral (w : WeightArray) (n : ℕ) (δ : ℝ) :
    lowRateDensity w n δ = ∫ x,
      (if 0 < stepProfile w n x ∧ stepProfile w n x < δ then (1 : ℝ) else 0)
      ∂profileMeasure
```

### integrable_lowProfile

lemma; [source line 29](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowRates.lean:29)

```lean
lemma integrable_lowProfile (w : WeightArray) (n : ℕ) (δ : ℝ) :
    Integrable (fun x => if 0 < stepProfile w n x ∧ stepProfile w n x < δ
      then (1 : ℝ) else 0) profileMeasure
```

### ProfileLimit.lowTriangle_tail

lemma; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowRates.lean:44)

Continuous triangular cutoffs shrink to zero at every positive profile
value. The limit's strict positivity is used precisely at this point.

```lean
lemma ProfileLimit.lowTriangle_tail {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) :
    Tendsto (fun K : ℕ => ∫ x, max (1 - K * f x) 0 ∂profileMeasure) atTop (𝓝 0)
```

### ProfileLimit.lowRateDensity_small

theorem; [source line 70](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LowRates.lean:70)

The low-rate assertion in (1174–1185), in quantified form. All choices
δ in the punctured interval share the same profile cutoff.

```lean
theorem ProfileLimit.lowRateDensity_small {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n : ℕ in atTop, lowRateDensity w n δ < ε
```


## Luce/Section5LuceTransfer.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LuceTransfer.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace Luce
```

### cycleCountVector_raceDraw_eq_rank

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LuceTransfer.lean:11)

Draw order and rank order are inverse permutations; their actual cycle
counts coincide. This identity also covers the common extension at ties.

```lean
theorem cycleCountVector_raceDraw_eq_rank {n : ℕ} (z : Fin n → ℝ) (L : ℕ) :
    cycleCountVector L (raceDraw z) = cycleCountVector L (raceRankPermutation z)
```

### luce_cycle_vector_map_eq

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LuceTransfer.lean:20)

```lean
theorem luce_cycle_vector_map_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ, P.real {ω | π ω = σ} = w.mass σ) (L : ℕ) :
    P.map (fun ω => cycleCountVector L (π ω)) =
      (exponentialRace w).map (fun z => cycleCountVector L (raceRankPermutation z))
```

### luce_cycle_test_integral_eq

theorem; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section5LuceTransfer.lean:37)

```lean
theorem luce_cycle_test_integral_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ, P.real {ω | π ω = σ} = w.mass σ)
    (L : ℕ) (F : (Fin L → ℕ) →ᵇ ℝ) :
    (∫ ω, F (cycleCountVector L (π ω)) ∂P) =
      ∫ z, F (cycleCountVector L (raceRankPermutation z)) ∂exponentialRace w
```


## Luce/Section5MarkedCoefficientLimit.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped ENNReal BigOperators Topology
namespace Luce
```

### profileGapCoefficient

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:20)

```lean
def profileGapCoefficient (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  rateKernel (profileQuantile profileMeasure f x) a /
    profileD profileMeasure f (profileQuantile profileMeasure f x)
```

### continuousOn_profileGapCoefficient

lemma; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:24)

```lean
lemma continuousOn_profileGapCoefficient {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) (M : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => profileGapCoefficient f z.1 z.2)
      (Icc (0 : ℝ) M ×ˢ Icc (0 : ℝ) α)
```

### profileGapCoefficient_uniform_rank_modulus

lemma; [source line 46](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:46)

```lean
lemma profileGapCoefficient_uniform_rank_modulus {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc (0 : ℝ) M, ∀ x ∈ Icc (0 : ℝ) α,
      ∀ y ∈ Icc (0 : ℝ) α, |x - y| < δ →
        |profileGapCoefficient f a x - profileGapCoefficient f a y| < ε
```

### DeletedShiftedCoefficientBad

def; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:59)

```lean
def DeletedShiftedCoefficientBad {n : ℕ} (w : Weights n) (f : ℝ → ℝ)
    (r : ℕ) (α M ε : ℝ) (old : Fin n → ℝ) : Prop :=
  ∃ removed : Finset (Fin n), removed.card ≤ r ∧
    ∃ t : ℝ, 0 ≤ t ∧ deletedEmpiricalArrival removed old t ≤ α ∧
      ∃ a ∈ Icc (0 : ℝ) M, ∃ y ∈ Icc (0 : ℝ) α,
        |deletedEmpiricalArrival removed old t - y| ≤ (r : ℝ) / n ∧
          ε ≤ |rateKernel t a / deletedEmpiricalRemaining w removed old t -
            profileGapCoefficient f a y|
```

### section5_uniform_shifted_gap_coefficient

theorem; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:69)

The finite deleted-rank shift is uniform over all actual configurations.

```lean
theorem section5_uniform_shifted_gap_coefficient
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {old | DeletedShiftedCoefficientBad (w n) f r α M ε old}) atTop (𝓝 0)
```

### markedGapScalar

def; [source line 99](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:99)

One coordinate of the actual finite marked-gap coefficient.

```lean
def markedGapScalar {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (old : Fin n → ℝ) (i : Fin n) (q : Fin (Finset.univ \ removed).card) : ℝ :=
  rateKernel (raceGapStart (compactDeletedClocks removed old) q) (w.rate i) /
    (raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) q / n)
```

### markedGapCoefficient_eq_prod_scalar

lemma; [source line 104](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:104)

```lean
lemma markedGapCoefficient_eq_prod_scalar {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n)
    (q : Fin r → Fin (Finset.univ \ removed).card) (old : Fin n → ℝ) :
    markedGapCoefficient w removed u q old = ∏ a, markedGapScalar w removed old (u a) (q a)
```

### ValidMarkedGapConfiguration

def; [source line 111](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:111)

Explicit finite validity conditions for the coefficient estimate.
This does not assert injectivity or assume any probability estimate.

```lean
def ValidMarkedGapConfiguration {n r : ℕ} (w : Weights n) (α M : ℝ)
    (removed : Finset (Fin n)) (u j : Fin r → Fin n)
    (q : Fin r → Fin (Finset.univ \ removed).card) : Prop :=
  removed.card ≤ r ∧ ∀ a, (q a).val + a.val = (j a).val ∧
    (j a).val + (1 : ℝ) ≤ α * n ∧ w.rate (u a) ≤ M
```

### MarkedCoefficientBad

def; [source line 117](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:117)

```lean
def MarkedCoefficientBad {n : ℕ} (w : Weights n) (f : ℝ → ℝ)
    (r : ℕ) (α M ε : ℝ) (old : Fin n → ℝ) : Prop :=
  ∃ removed : Finset (Fin n), ∃ u j : Fin r → Fin n,
    ∃ q : Fin r → Fin (Finset.univ \ removed).card,
      ValidMarkedGapConfiguration w α M removed u j q ∧
        ∃ a, ε ≤ |markedGapScalar w removed old (u a) (q a) -
          profileGapCoefficient f (w.rate (u a)) (((j a).val + (1 : ℝ)) / n)|
```

### marked_raceGapStart_eq_consecutiveGapLower

lemma; [source line 125](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:125)

```lean
lemma marked_raceGapStart_eq_consecutiveGapLower {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (q : Fin m) :
    raceGapStart times q = consecutiveGapLower times htimes q
```

### markedGapScalar_eq_deleted

lemma; [source line 130](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:130)

```lean
lemma markedGapScalar_eq_deleted {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (old : Fin n → ℝ) (hold : Injective old) (hpos : ∀ i, 0 < old i)
    (i : Fin n) (q : Fin (Finset.univ \ removed).card) :
    markedGapScalar w removed old i q =
      rateKernel (consecutiveGapLower (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold) q) (w.rate i) /
      deletedEmpiricalRemaining w removed old
        (consecutiveGapLower (compactDeletedClocks removed old)
          (compactDeletedClocks_injective removed old hold) q)
```

### validMarkedGap_coordinates

lemma; [source line 145](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:145)

Exact finite arithmetic at the marked gap's lower endpoint.

```lean
lemma validMarkedGap_coordinates {n r : ℕ} (w : Weights n) (hn : 0 < n)
    {α M : ℝ} (removed : Finset (Fin n)) (u j : Fin r → Fin n)
    (q : Fin r → Fin (Finset.univ \ removed).card)
    (hv : ValidMarkedGapConfiguration w α M removed u j q)
    (old : Fin n → ℝ) (hold : Injective old) (hpos : ∀ i, 0 < old i) (a : Fin r) :
    let t
```

### section5_uniform_marked_gap_coefficient

theorem; [source line 173](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:173)

Every bounded sorted marked configuration is controlled by one global
bad event. The probability tends to zero uniformly over all configurations
and all marked coordinates, at the original prescribed rank `(j+1)/n`.

```lean
theorem section5_uniform_marked_gap_coefficient
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w n)
      {old | MarkedCoefficientBad (w n) f r α M ε old}) atTop (𝓝 0)
```

### ProfileLimit.marked_gap_scalar_uniform_bound

theorem; [source line 199](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedCoefficientLimit.lean:199)

A fixed deterministic envelope for both actual and target scalar
coefficients. Every probabilistic background satisfies the two explicit
clock conditions almost surely under the proved exponential law.

```lean
theorem ProfileLimit.marked_gap_scalar_uniform_bound {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ removed : Finset (Fin n), ∀ u j : Fin r → Fin n,
        ∀ q : Fin r → Fin (Finset.univ \ removed).card,
          ValidMarkedGapConfiguration (w n) α M removed u j q →
            ∀ old : Fin n → ℝ, Injective old → (∀ i, 0 < old i) → ∀ a,
              |markedGapScalar (w n) removed old (u a) (q a)| ≤ C ∧
              |profileGapCoefficient f ((w n).rate (u a)) (((j a).val + (1 : ℝ)) / n)| ≤ C
```


## Luce/Section5MarkedExpectation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedExpectation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped BigOperators Topology ENNReal
namespace Luce
```

### MarkedGapIndexData

structure; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedExpectation.lean:23)

Finite index data for a selection of distinct deleted gaps. This
auxiliary representation contains no probability or convergence facts.

```lean
structure MarkedGapIndexData (n r : ℕ) where
  removed : Finset (Fin n)
  labels : Fin r → Fin n
  ranks : Fin r → Fin n
  gaps : Fin r ↪ Fin (Finset.univ \ removed).card
```

### section5_marked_coefficient_expectation

theorem; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedExpectation.lean:31)

Uniform expectation convergence for the actual coefficient and actual
normalized gaps, with their moment hypotheses fully discharged.

```lean
theorem section5_marked_coefficient_expectation
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ removed : Finset (Fin n), ∀ u j : Fin r → Fin n,
        ∀ q : Fin r ↪ Fin (Finset.univ \ removed).card,
          ValidMarkedGapConfiguration (w n) α M removed u j q →
            (∫ old, |markedGapCoefficient (w n) removed u q old -
                ∏ a, profileGapCoefficient f ((w n).rate (u a))
                  (((j a).val + (1 : ℝ)) / n)| *
              (∏ a, markedNormalizedGaps (w n) removed q old a) ∂exponentialRace (w n)) < ε
```


## Luce/Section5MarkedGapBridge.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGapBridge.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce
```

### sum_deletedClockLabel

lemma; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGapBridge.lean:21)

```lean
lemma sum_deletedClockLabel {n : ℕ} (removed : Finset (Fin n)) (g : Fin n → ℝ) :
    (∑ k, g (deletedClockLabel removed k)) = ∑ i ∈ Finset.univ \ removed, g i
```

### consecutiveGapLower_eq_previous

lemma; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGapBridge.lean:26)

```lean
lemma consecutiveGapLower_eq_previous {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (q : Fin m) :
    consecutiveGapLower times htimes q =
      previousOrderedTime (fun k => times (drawPermutation times htimes k)) q
```

### consecutiveGapLower_le_upper

lemma; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGapBridge.lean:33)

```lean
lemma consecutiveGapLower_le_upper {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (hpos : ∀ i, 0 ≤ times i) (q : Fin m) :
    consecutiveGapLower times htimes q ≤ arrivalTime times htimes q
```

### deletedGapKernel_toReal_eq_exponentialGapMass

theorem; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGapBridge.lean:45)

The exact kernel is the actual exponential mass of this consecutive
gap; the duration is proved nonnegative before applying Taylor estimates.

```lean
theorem deletedGapKernel_toReal_eq_exponentialGapMass {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hold : Injective old)
    (hpos : ∀ i, 0 ≤ old i) (i : Fin n) (q : Fin (Finset.univ \ removed).card) :
    (deletedGapKernel w removed old i q.val).toReal =
      exponentialGapMass (w.rate i)
        (consecutiveGapLower (compactDeletedClocks removed old)
          (compactDeletedClocks_injective removed old hold) q)
        (arrivalTime (compactDeletedClocks removed old)
            (compactDeletedClocks_injective removed old hold) q -
          consecutiveGapLower (compactDeletedClocks removed old)
            (compactDeletedClocks_injective removed old hold) q)
```

### deletedEmpiricalArrival_gapUpper

theorem; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGapBridge.lean:66)

The deleted CDF at the upper endpoint T_(q+1) is `(q+1)/n` with
the original row-size normalization.

```lean
theorem deletedEmpiricalArrival_gapUpper {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (hold : Injective old) (q : Fin (Finset.univ \ removed).card) :
    deletedEmpiricalArrival removed old
      (arrivalTime (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold) q) = ((q.val : ℝ) + 1) / n
```

### deletedEmpiricalArrival_gapLower

theorem; [source line 88](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGapBridge.lean:88)

The deleted CDF at the lower endpoint T_q is exactly `q/n`.
Strict positivity handles T₀=0 without an extra initial atom.

```lean
theorem deletedEmpiricalArrival_gapLower {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (hold : Injective old) (hpos : ∀ i, 0 < old i)
    (q : Fin (Finset.univ \ removed).card) :
    deletedEmpiricalArrival removed old
      (consecutiveGapLower (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold) q) = (q.val : ℝ) / n
```

### orderedNormalizedGaps_compactDeleted

theorem; [source line 108](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGapBridge.lean:108)

The normalized gap variable is the actual rate times the exact finite
gap duration used above. This fixes the zero-based gap orientation.

```lean
theorem orderedNormalizedGaps_compactDeleted {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hold : Injective old)
    (q : Fin (Finset.univ \ removed).card) :
    orderedNormalizedGaps (compactDeletedWeights w removed)
      (drawPermutation (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold))
      (compactDeletedClocks removed old) q =
      orderedRemainingRate (compactDeletedWeights w removed)
        (drawPermutation (compactDeletedClocks removed old)
          (compactDeletedClocks_injective removed old hold)) q *
        (arrivalTime (compactDeletedClocks removed old)
            (compactDeletedClocks_injective removed old hold) q -
          consecutiveGapLower (compactDeletedClocks removed old)
            (compactDeletedClocks_injective removed old hold) q)
```

### arrivalTime_strictMono

lemma; [source line 125](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGapBridge.lean:125)

```lean
lemma arrivalTime_strictMono {m : ℕ} (times : Fin m → ℝ) (htimes : Injective times) :
    StrictMono (arrivalTime times htimes)
```

### deletedEmpiricalRemaining_gapLower

theorem; [source line 133](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGapBridge.lean:133)

Just after T_q the unmarked strict-survival rate is exactly W_q.
The denominator remains the original n, as required by the deleted race LLN.

```lean
theorem deletedEmpiricalRemaining_gapLower {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hold : Injective old)
    (hpos : ∀ i, 0 < old i) (q : Fin (Finset.univ \ removed).card) :
    deletedEmpiricalRemaining w removed old
      (consecutiveGapLower (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold) q) =
      orderedRemainingRate (compactDeletedWeights w removed)
        (drawPermutation (compactDeletedClocks removed old)
          (compactDeletedClocks_injective removed old hold)) q / n
```


## Luce/Section5MarkedGaps.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce
```

### deletedBeforeCount

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:21)

Unmarked clocks strictly before an insertion time.

```lean
def deletedBeforeCount {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (t : ℝ) : ℕ :=
  ((Finset.univ \ removed).filter fun i => old i < t).card
```

### deletedBeforeCount_mono

lemma; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:25)

```lean
lemma deletedBeforeCount_mono {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) : Monotone (deletedBeforeCount removed old)
```

### deletedBeforeCount_eq_of_eq_off

lemma; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:33)

```lean
lemma deletedBeforeCount_eq_of_eq_off {n : ℕ} (removed : Finset (Fin n))
    (old new : Fin n → ℝ) (hsame : ∀ i, i ∉ removed → new i = old i) (t : ℝ) :
    deletedBeforeCount removed new t = deletedBeforeCount removed old t
```

### clockBeforeCount_eq_deleted_add_marked

lemma; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:44)

Exact accounting for every marked clock; injectivity discharges all
image multiplicities.

```lean
lemma clockBeforeCount_eq_deleted_add_marked {n r : ℕ} (u : Fin r → Fin n)
    (hu : Injective u) (clocks : Fin n → ℝ) (t : ℝ) :
    clockBeforeCount clocks t = deletedBeforeCount (Finset.univ.image u) clocks t +
      ∑ a : Fin r, if clocks (u a) < t then 1 else 0
```

### markedBeforeCount_eq_index

lemma; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:54)

```lean
lemma markedBeforeCount_eq_index {n r : ℕ} (u : Fin r → Fin n)
    (clocks : Fin n → ℝ) (hordered : StrictMono (fun a => clocks (u a))) (a : Fin r) :
    (∑ b : Fin r, if clocks (u b) < clocks (u a) then 1 else 0) = a.val
```

### marked_times_strictMono_of_rankCylinder

lemma; [source line 66](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:66)

Sorted prescribed ranks force sorted marked times, including for
arbitrary deterministic backgrounds.

```lean
lemma marked_times_strictMono_of_rankCylinder {n r : ℕ}
    (u j : Fin r → Fin n) (clocks : Fin n → ℝ)
    (hj : StrictMono j) (h : MarkedRankCylinder u j clocks) :
    StrictMono (fun a => clocks (u a))
```

### markedRankCylinder_deleted_counts

theorem; [source line 83](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:83)

Deleting the `a` earlier marked clocks gives gap number `j_a-a`.
The one-based paper position is `a.val+1` and its rank is `(j a).val+1`.

```lean
theorem markedRankCylinder_deleted_counts {n r : ℕ} (u j : Fin r → Fin n)
    (hu : Injective u) (hj : StrictMono j) (clocks : Fin n → ℝ)
    (h : MarkedRankCylinder u j clocks) :
    ∀ a, deletedBeforeCount (Finset.univ.image u) clocks (clocks (u a)) =
      (j a).val - a.val
```

### marked_times_strictMono_of_deleted_counts

lemma; [source line 97](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:97)

Different ordered gap numbers force different ordered insertion times.

```lean
lemma marked_times_strictMono_of_deleted_counts {n r : ℕ}
    (u : Fin r → Fin n) (q : Fin r → ℕ) (hq : StrictMono q)
    (clocks : Fin n → ℝ)
    (h : ∀ a, deletedBeforeCount (Finset.univ.image u) clocks (clocks (u a)) = q a) :
    StrictMono (fun a => clocks (u a))
```

### markedRankCylinder_iff_deleted_counts

theorem; [source line 111](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:111)

Exact deterministic insertion identity when the relevant deleted gaps
are distinct. The arithmetic identity exposes the rank convention rather
than relying on truncated subtraction.

```lean
theorem markedRankCylinder_iff_deleted_counts {n r : ℕ} (u j : Fin r → Fin n)
    (hu : Injective u) (hj : StrictMono j) (q : Fin r → ℕ)
    (hq : StrictMono q) (hindex : ∀ a, q a + a.val = (j a).val)
    (clocks : Fin n → ℝ) :
    MarkedRankCylinder u j clocks ↔
      ∀ a, deletedBeforeCount (Finset.univ.image u) clocks (clocks (u a)) = q a
```

### measurable_deletedBeforeCount

lemma; [source line 130](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:130)

```lean
lemma measurable_deletedBeforeCount {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (removed : Finset (Fin n)) (old : Ω → Fin n → ℝ) (t : Ω → ℝ)
    (hold : ∀ i, Measurable (fun x => old x i)) (ht : Measurable t) :
    Measurable (fun x => deletedBeforeCount removed (old x) (t x))
```

### DeletedGapCount

def; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:141)

Membership in the exact deleted gap, with both its endpoints excluded
almost surely. Endpoint correspondence is proved below.

```lean
def DeletedGapCount {n : ℕ} (removed : Finset (Fin n)) (old : Fin n → ℝ)
    (q : ℕ) (t : ℝ) : Prop := 0 < t ∧ deletedBeforeCount removed old t = q
```

### measurableSet_deletedGapCount

lemma; [source line 144](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:144)

```lean
lemma measurableSet_deletedGapCount {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (removed : Finset (Fin n)) (old : Ω → Fin n → ℝ) (q : ℕ) (t : Ω → ℝ)
    (hold : ∀ i, Measurable (fun x => old x i)) (ht : Measurable t) :
    MeasurableSet {x | DeletedGapCount removed (old x) q (t x)}
```

### deletedGapKernel

def; [source line 152](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:152)

Probability mass of a single exact deleted gap.

```lean
def deletedGapKernel {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (old : Fin n → ℝ) (i : Fin n) (q : ℕ) : ℝ≥0∞ :=
  expMeasure (w.rate i) {t | DeletedGapCount removed old q t}
```

### deletedGapKernel_le_one

lemma; [source line 156](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:156)

```lean
lemma deletedGapKernel_le_one {n : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (old : Fin n → ℝ) (i : Fin n) (q : ℕ) : deletedGapKernel w removed old i q ≤ 1
```

### measurable_deletedGapKernel

lemma; [source line 161](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:161)

```lean
lemma measurable_deletedGapKernel {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n) (q : ℕ) :
    Measurable (fun old => deletedGapKernel w removed old i q)
```

### deletedGapKernel_marked_product

theorem; [source line 171](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:171)

The exact deleted-gap mass product is a conditional probability.

```lean
theorem deletedGapKernel_marked_product {n r : ℕ} (w : Weights n)
    (old : Fin n → ℝ) (u : Fin r → Fin n) (q : Fin r → ℕ) (hu : Injective u) :
    exponentialRace w {fresh | ∀ a,
      DeletedGapCount (Finset.univ.image u) old (q a) (fresh (u a))} =
      ∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a)
```

### DeletedMarkedSuccess

def; [source line 192](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:192)

```lean
def DeletedMarkedSuccess {n r : ℕ} (u : Fin r → Fin n) (q : Fin r → ℕ)
    (c : Fin n → ℝ × ℝ) : Prop :=
  ∀ a, DeletedGapCount (Finset.univ.image u) (fun i => (c i).1) (q a) (c (u a)).2
```

### measurableSet_deletedMarkedSuccess

lemma; [source line 196](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:196)

```lean
lemma measurableSet_deletedMarkedSuccess {n r : ℕ} (u : Fin r → Fin n) (q : Fin r → ℕ) :
    MeasurableSet {c | DeletedMarkedSuccess u q c}
```

### lintegral_deletedGapKernel_product

theorem; [source line 208](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:208)

Tonelli uses the original independent clock family, with the unused
marked background coordinates integrated out.

```lean
theorem lintegral_deletedGapKernel_product {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (hu : Injective u) :
    (∫⁻ old, ∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a)
      ∂exponentialRace w) = pairedExponentialRace w {c | DeletedMarkedSuccess u q c}
```

### swapped_deleted_count

lemma; [source line 233](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:233)

```lean
lemma swapped_deleted_count {n r : ℕ} (u : Fin r → Fin n)
    (c : Fin n → ℝ × ℝ) (t : ℝ) :
    deletedBeforeCount (Finset.univ.image u)
      (fun i => (swapClockCopies (Finset.univ.image u) c i).1) t =
      deletedBeforeCount (Finset.univ.image u) (fun i => (c i).1) t
```

### swapped_markedRankCylinder_iff_deleted_success

theorem; [source line 243](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:243)

The exact event identity after resampling distinct marked labels.

```lean
theorem swapped_markedRankCylinder_iff_deleted_success {n r : ℕ}
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r → ℕ) (hq : StrictMono q) (hindex : ∀ a, q a + a.val = (j a).val)
    (c : Fin n → ℝ × ℝ)
    (hpos : ∀ i, 0 < (swapClockCopies (Finset.univ.image u) c i).1) :
    MarkedRankCylinder u j (fun i => (swapClockCopies (Finset.univ.image u) c i).1) ↔
      DeletedMarkedSuccess u q c
```

### markedRankCylinder_probability_eq_deletedGapProduct

theorem; [source line 262](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:262)

The paper's exact insertion identity for separated marked gaps. It
holds for the actual exponential race and actual deleted-gap masses.

```lean
theorem markedRankCylinder_probability_eq_deletedGapProduct {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r → ℕ) (hq : StrictMono q) (hindex : ∀ a, q a + a.val = (j a).val) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} =
      ∫⁻ old, ∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a)
        ∂exponentialRace w
```

### markedRankCylinder_probability_le_deletedGapProduct

theorem; [source line 283](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:283)

Without separated gaps only inclusion is asserted: several marked
clocks may enter the same gap and still need the prescribed internal order.
Dropping that order gives the bound used for the weighted cylinder estimate.

```lean
theorem markedRankCylinder_probability_le_deletedGapProduct {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r → ℕ) (hindex : ∀ a, q a + a.val = (j a).val) :
    exponentialRace w {clocks | MarkedRankCylinder u j clocks} ≤
      ∫⁻ old, ∏ a, deletedGapKernel w (Finset.univ.image u) old (u a) (q a)
        ∂exponentialRace w
```

### deletedGapProduct_integrable

lemma; [source line 309](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:309)

```lean
lemma deletedGapProduct_integrable {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n) (q : Fin r → ℕ) :
    Integrable (fun old => ∏ a, (deletedGapKernel w removed old (u a) (q a)).toReal)
      (exponentialRace w)
```

### markedRankCylinder_real_probability_eq_deletedGapProduct

theorem; [source line 321](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedGaps.lean:321)

```lean
theorem markedRankCylinder_real_probability_eq_deletedGapProduct {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : StrictMono j)
    (q : Fin r → ℕ) (hq : StrictMono q) (hindex : ∀ a, q a + a.val = (j a).val) :
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} =
      ∫ old, ∏ a, (deletedGapKernel w (Finset.univ.image u) old (u a) (q a)).toReal
        ∂exponentialRace w
```


## Luce/Section5MarkedSort.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedSort.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Function
open scoped BigOperators
namespace Luce
```

### markedRankCylinder_comp_perm

lemma; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedSort.lean:13)

```lean
lemma markedRankCylinder_comp_perm {n r : ℕ} (u j : Fin r → Fin n)
    (e : Equiv.Perm (Fin r)) (old : Fin n → ℝ) :
    MarkedRankCylinder (u ∘ e) (j ∘ e) old ↔ MarkedRankCylinder u j old
```

### markedImage_comp_perm

lemma; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedSort.lean:22)

```lean
lemma markedImage_comp_perm {n r : ℕ} (u : Fin r → Fin n) (e : Equiv.Perm (Fin r)) :
    Finset.univ.image (u ∘ e) = Finset.univ.image u
```

### strictMono_sorted_markedRanks

lemma; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedSort.lean:32)

```lean
lemma strictMono_sorted_markedRanks {n r : ℕ} (j : Fin r → Fin n) (hj : Injective j) :
    StrictMono (j ∘ Tuple.sort j)
```

### index_le_of_strictMono_ranks

lemma; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedSort.lean:38)

A strictly increasing sequence of natural rank positions has at least
`a` entries before its `a`th value. This proves subtraction is not truncated.

```lean
lemma index_le_of_strictMono_ranks {n r : ℕ} (j : Fin r → Fin n)
    (hj : StrictMono j) (a : Fin r) : a.val ≤ (j a).val
```

### sortedMarkedGapIndex

def; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedSort.lean:48)

```lean
def sortedMarkedGapIndex {n r : ℕ} (j : Fin r → Fin n) (a : Fin r) : ℕ :=
  (j (Tuple.sort j a)).val - a.val
```

### sortedMarkedGapIndex_add

lemma; [source line 51](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedSort.lean:51)

```lean
lemma sortedMarkedGapIndex_add {n r : ℕ} (j : Fin r → Fin n) (hj : Injective j) (a : Fin r) :
    sortedMarkedGapIndex j a + a.val = (j (Tuple.sort j a)).val
```

### sortedMarkedGapIndex_strictMono

lemma; [source line 57](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedSort.lean:57)

Macroscopic rank separation eventually implies this finite condition:
rank distances at least `r` force all deleted gap numbers to be distinct.

```lean
lemma sortedMarkedGapIndex_strictMono {n r : ℕ} (j : Fin r → Fin n) (hj : Injective j)
    (hsep : ∀ a b, a ≠ b → r ≤ Nat.dist (j a).val (j b).val) :
    StrictMono (sortedMarkedGapIndex j)
```

### sortedMarkedGapIndex_lt_complement

lemma; [source line 71](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedSort.lean:71)

Finite bulk margin excludes the terminal deleted gap.

```lean
lemma sortedMarkedGapIndex_lt_complement {n r : ℕ} (u j : Fin r → Fin n)
    (hu : Injective u) (hbulk : ∀ a, (j a).val + r < n) (a : Fin r) :
    sortedMarkedGapIndex j a < (Finset.univ \ Finset.univ.image u).card
```

### markedRankCylinder_probability_eq_sortedGapProduct

theorem; [source line 81](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MarkedSort.lean:81)

Exact marked insertion identity with sorting and gap indices derived
from the original arbitrary injective target tuple.

```lean
theorem markedRankCylinder_probability_eq_sortedGapProduct {n r : ℕ} (w : Weights n)
    (u j : Fin r → Fin n) (hu : Injective u) (hj : Injective j)
    (hsep : ∀ a b, a ≠ b → r ≤ Nat.dist (j a).val (j b).val) :
    exponentialRace w {old | MarkedRankCylinder u j old} =
      ∫⁻ old, ∏ a, deletedGapKernel w (Finset.univ.image u) old
        (u (Tuple.sort j a)) (sortedMarkedGapIndex j a) ∂exponentialRace w
```


## Luce/Section5MaximumCylinder.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumCylinder.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace Luce
```

### retainedMaximumCycleEvent

def; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumCylinder.lean:12)

Actual retained cycles rooted at their largest label. S restricts only
cycle vertices, never the background rates or clocks.

```lean
def retainedMaximumCycleEvent {n : ℕ} (k : ℕ) (S : Finset (Fin n)) (v : Fin n) :
    Set (Fin n → ℝ) :=
  {e | minimalPeriod (raceRankPermutation e : Fin n → Fin n) v = k+1 ∧
    (∀ u ∈ (periodicOrbit (raceRankPermutation e : Fin n → Fin n) v).toFinset, u ≤ v) ∧
    (periodicOrbit (raceRankPermutation e : Fin n → Fin n) v).toFinset ⊆ S}
```

### retainedMaximumCycleEvent_eq_actual_roots

theorem; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumCylinder.lean:18)

```lean
theorem retainedMaximumCycleEvent_eq_actual_roots {n : ℕ} (k : ℕ)
    (S : Finset (Fin n)) (v : Fin n) :
    retainedMaximumCycleEvent k S v =
      {e | v ∈ Section5.maximumCycleRoots (raceRankPermutation e) k ∧
        (periodicOrbit (raceRankPermutation e : Fin n → Fin n) v).toFinset ⊆ S}
```

### measurableSet_retainedMaximumCycleEvent

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumCylinder.lean:27)

```lean
theorem measurableSet_retainedMaximumCycleEvent {n : ℕ} (k : ℕ)
    (S : Finset (Fin n)) (v : Fin n) : MeasurableSet (retainedMaximumCycleEvent k S v)
```

### exists_retained_maximum_cycle_tail

theorem; [source line 35](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumCylinder.lean:35)

```lean
theorem exists_retained_maximum_cycle_tail {n k : ℕ} (R : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (v : Fin n)
    (hp : minimalPeriod (R : Fin n → Fin n) v = k+1)
    (hmax : ∀ u ∈ (periodicOrbit (R : Fin n → Fin n) v).toFinset, u ≤ v)
    (hS : (periodicOrbit (R : Fin n → Fin n) v).toFinset ⊆ S) :
    ∃ u : Fin k → Fin n, Injective u ∧ (∀ a, u a < v) ∧
      (∀ a, (Fin.cons v u : Fin (k+1) → Fin n) a ∈ S) ∧
      ∀ a, R ((Fin.cons v u : Fin (k+1) → Fin n) a) =
        (Fin.snoc u v : Fin (k+1) → Fin n) a
```

### retained_maximum_cycle_probability_le_ghost

theorem; [source line 65](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumCylinder.lean:65)

Restricted maximum-root cylinder bound on one common ghost background.
The inequalities u(a) < v remain in the finite sum.

```lean
theorem retained_maximum_cycle_probability_le_ghost {n : ℕ} (w : Weights n)
    (k : ℕ) (S : Finset (Fin n)) (v : Fin n) :
    (exponentialRace w).real (retainedMaximumCycleEvent k S v) ≤
      ∫ old, ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        Injective u ∧ (∀ a, u a < v) ∧
          ∀ a, (Fin.cons v u : Fin (k+1) → Fin n) a ∈ S),
        ∏ a : Fin (k+1), ghostEntry w (k+1) old
          ((Fin.cons v u : Fin (k+1) → Fin n) a)
          ((Fin.snoc u v : Fin (k+1) → Fin n) a) ∂exponentialRace w
```


## Luce/Section5MaximumExpectation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumExpectation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section5
```

### tailCycleExpectation_eq_maximum_probability_sum

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumExpectation.lean:11)

The expected number of cycles meeting the tail is the sum of the
actual maximum-root event probabilities. The cutoff is not approximated.

```lean
theorem tailCycleExpectation_eq_maximum_probability_sum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) _ ⊤ π) (k : ℕ) (α : ℝ) :
    (∫ ω, ((cycleCount (π ω) k - bulkCycleCount (π ω) α k : ℕ) : ℝ) ∂P) =
      ∑ v : Fin n, P.real {ω | v ∈ maximumCycleRoots (π ω) k ∧ α*n < (v.val : ℝ)+1}
```


## Luce/Section5MaximumReturn.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumReturn.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open scoped BigOperators
namespace Luce
```

### retained_maximum_ghost_sum_le_return

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumReturn.lean:11)

Drop only the internal distinctness and retention restrictions. The
marked predecessor u remains retained and strictly below the maximum v.

```lean
theorem retained_maximum_ghost_sum_le_return {n : ℕ} (w : Weights n)
    (k : ℕ) (S : Finset (Fin n)) (old : Fin n → ℝ) (v : Fin n) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin (k+1) → Fin n =>
      Function.Injective u ∧ (∀ a, u a < v) ∧
        ∀ a, (Fin.cons v u : Fin (k+2) → Fin n) a ∈ S),
      ∏ a : Fin (k+2), ghostEntry w (k+2) old
        ((Fin.cons v u : Fin (k+2) → Fin n) a)
        ((Fin.snoc u v : Fin (k+2) → Fin n) a)) ≤
      ∑ u : Fin n, if u ∈ S ∧ u < v then
        ghostEntry w (k+2) old u v * markedReturnWeight (ghostEntry w (k+2) old) k v u else 0
```


## Luce/Section5MaximumReturnExpectation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumReturnExpectation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### marked_return_product_eq_cylinder_sum

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumReturnExpectation.lean:9)

```lean
theorem marked_return_product_eq_cylinder_sum {n : ℕ} (w : Weights n)
    (k : ℕ) (old : Fin n → ℝ) (v u : Fin n) :
    ghostEntry w (k+2) old u v * markedReturnWeight (ghostEntry w (k+2) old) k v u =
      ∑ t : Fin k → Fin n, ∏ a : Fin (k+2), ghostEntry w (k+2) old
        ((Fin.cons v (Fin.snoc t u) : Fin (k+2) → Fin n) a)
        ((Fin.snoc (Fin.snoc t u) v : Fin (k+2) → Fin n) a)
```

### integrable_marked_return_product

theorem; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumReturnExpectation.lean:22)

```lean
theorem integrable_marked_return_product {n : ℕ} (w : Weights n)
    (k : ℕ) (v u : Fin n) :
    Integrable (fun old => ghostEntry w (k+2) old u v *
      markedReturnWeight (ghostEntry w (k+2) old) k v u) (exponentialRace w)
```

### retained_maximum_cycle_probability_le_return

theorem; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumReturnExpectation.lean:32)

The actual retained maximum-cycle probability is bounded by the
integrated marked edge and return paths, with u retained and u < v.
All integrability premises are proved from the canonical race.

```lean
theorem retained_maximum_cycle_probability_le_return {n : ℕ} (w : Weights n)
    (k : ℕ) (S : Finset (Fin n)) (v : Fin n) :
    (exponentialRace w).real (retainedMaximumCycleEvent (k+1) S v) ≤
      ∫ old, ∑ u : Fin n, if u ∈ S ∧ u < v then
        ghostEntry w (k+2) old u v * markedReturnWeight (ghostEntry w (k+2) old) k v u
        else 0 ∂exponentialRace w
```


## Luce/Section5MaximumRoot.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Function
open scoped BigOperators
namespace Luce.Section5
```

### cycleMaximum

def; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:9)

```lean
def cycleMaximum {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(cycleOrbits R k)) : Fin n :=
  c.val.toFinset.max' (Finset.card_pos.mp (by rw [cycleOrbit_card R k c.val c.property]; omega))
```

### cycleMaximum_mem

theorem; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:13)

```lean
theorem cycleMaximum_mem {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(cycleOrbits R k)) : cycleMaximum R k c ∈ c.val.toFinset
```

### cycleMaximum_upper

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:17)

```lean
theorem cycleMaximum_upper {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(cycleOrbits R k)) (v : Fin n) (hv : v ∈ c.val.toFinset) :
    v ≤ cycleMaximum R k c
```

### cycleMaximum_orbit

theorem; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:21)

```lean
theorem cycleMaximum_orbit {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(cycleOrbits R k)) : periodicOrbit (R : Fin n → Fin n) (cycleMaximum R k c) = c.val
```

### cycleMaximum_injective

theorem; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:25)

```lean
theorem cycleMaximum_injective {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ) :
    Injective (cycleMaximum R k)
```

### maximumCycleRoots

def; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:33)

Each unrooted cycle contributes exactly one largest label. No symmetry
factor remains after this choice of root.

```lean
def maximumCycleRoots {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.image (cycleMaximum R k)
```

### maximumCycleRoots_card

theorem; [source line 37](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:37)

```lean
theorem maximumCycleRoots_card {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ) :
    (maximumCycleRoots R k).card = cycleCount R k
```

### cycleMaximum_cutoff_iff

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:43)

```lean
theorem cycleMaximum_cutoff_iff {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(cycleOrbits R k)) (α : ℝ) :
    c.val.toFinset ⊆ bulkCycleLabelSet n α ↔
      ((cycleMaximum R k c).val : ℝ)+1 ≤ α*n
```

### bulkCycleCount_eq_maximum_roots

theorem; [source line 59](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:59)

Exact cutoff cycle count as a count of maximum roots.

```lean
theorem bulkCycleCount_eq_maximum_roots {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (α : ℝ) :
    bulkCycleCount R α k = ((maximumCycleRoots R k).filter
      (fun v => (v.val : ℝ)+1 ≤ α*n)).card
```

### tailCycleCount_eq_maximum_roots

theorem; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:84)

Exact number of cycles meeting the terminal interval, represented by
their unique largest labels. The natural subtraction is justified by the
finite partition, without a new hypothesis about the cutoff.

```lean
theorem tailCycleCount_eq_maximum_roots {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (α : ℝ) :
    cycleCount R k - bulkCycleCount R α k =
      ((maximumCycleRoots R k).filter (fun v => α*n < (v.val : ℝ)+1)).card
```

### mem_maximumCycleRoots_iff

theorem; [source line 95](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumRoot.lean:95)

```lean
theorem mem_maximumCycleRoots_iff {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ) (v : Fin n) :
    v ∈ maximumCycleRoots R k ↔
      minimalPeriod (R : Fin n → Fin n) v = k+1 ∧
      ∀ u ∈ (periodicOrbit (R : Fin n → Fin n) v).toFinset, u ≤ v
```


## Luce/Section5MaximumTimeSplit.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumTimeSplit.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### retained_maximum_probability_sum_le_time_split

theorem; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MaximumTimeSplit.lean:11)

Split the actual retained maximum-cycle probability sum at arbitrary
target cutoffs. Every probability and return weight is the existing one.

```lean
theorem retained_maximum_probability_sum_le_time_split {n : ℕ} (w : Weights n)
    (k : ℕ) (S T : Finset (Fin n)) (cut : Fin n → ℝ) :
    (∑ v ∈ T, (exponentialRace w).real (retainedMaximumCycleEvent (k+1) S v)) ≤
      (∫ old, ∑ v ∈ T, ∑ u ∈ S.filter (fun u => u < v),
        earlyGhostKernel w (k+2) old u v (cut v) *
          markedReturnWeight (ghostEntry w (k+2) old) k v u ∂exponentialRace w) +
      (∫ old, ∑ v ∈ T, ∑ u ∈ S.filter (fun u => u < v),
        lateGhostKernel w (k+2) old u v (cut v) *
          markedReturnWeight (ghostEntry w (k+2) old) k v u ∂exponentialRace w)
```


## Luce/Section5Microscopic.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Microscopic.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology BigOperators
namespace Luce
```

### section5_sorted_marked_asymptotic

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Microscopic.lean:24)

Uniform local estimate in sorted-rank notation. No convergence,
moment, rate reservoir, or independence premise remains. The explicit
finite gap indices are derived from separated ranks in the next step.

```lean
theorem section5_sorted_marked_asymptotic
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ u j : Fin r → Fin n, Injective u → StrictMono j →
        ∀ q : Fin r ↪ Fin (Finset.univ \ Finset.univ.image u).card,
          StrictMono (fun a => (q a).val) → (∀ a, (q a).val + a.val = (j a).val) →
            (∀ a, (w n).rate (u a) ≤ M) → (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
              |(n : ℝ) ^ r * (exponentialRace (w n)).real {old | MarkedRankCylinder u j old} -
                ∏ a, profileGapCoefficient f ((w n).rate (u a))
                  (((j a).val + (1 : ℝ)) / n)| < ε
```


## Luce/Section5MicroscopicSort.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MicroscopicSort.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Function Filter Set
open scoped BigOperators Topology
namespace Luce
```

### real_coe_nat_dist

lemma; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MicroscopicSort.lean:21)

```lean
lemma real_coe_nat_dist (a b : ℕ) : (Nat.dist a b : ℝ) = |(a : ℝ) - b|
```

### bounded_marked_asymptotic_of_sorted

theorem; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section5MicroscopicSort.lean:32)

An auxiliary reduction from a proved sorted finite-gap estimate.
The main microscopic theorem must discharge `hsorted`; it is not an
assumed spacing law or a claimed completed asymptotic.

```lean
theorem bounded_marked_asymptotic_of_sorted
    (w : WeightArray) (f : ℝ → ℝ) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ)
    (hsorted : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ u j : Fin r → Fin n, Injective u → StrictMono j →
        ∀ q : Fin r ↪ Fin (Finset.univ \ Finset.univ.image u).card,
          StrictMono (fun a => (q a).val) →
          (∀ a, (q a).val + a.val = (j a).val) →
          (∀ a, (w n).rate (u a) ≤ M) →
          (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
          |(n : ℝ) ^ r * (exponentialRace (w n)).real {old | MarkedRankCylinder u j old} -
            ∏ a, profileGapCoefficient f ((w n).rate (u a))
              (((j a).val + (1 : ℝ)) / n)| < ε) :
    ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a, (w n).rate (i a) ≤ M) →
        (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
        (∀ a b, a ≠ b → ζ * n ≤ |((j a).val : ℝ) - (j b).val|) →
        |(n : ℝ) ^ r * (exponentialRace (w n)).real
            {old | ∀ a, raceRank old (i a) = (j a).val + 1} -
          ∏ a, finiteCyclicDensity (w n) f (i a) (j a)| < ε
```


## Luce/Section5Occupation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce
```

### clockBeforeCount_eq_candidate_add_background

lemma; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:20)

```lean
lemma clockBeforeCount_eq_candidate_add_background {n : ℕ}
    (clocks : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (t : ℝ) :
    clockBeforeCount clocks t = (if clocks i < t then 1 else 0) +
      clockBeforeCount (fun j => clocks (i.succAbove j)) t
```

### clockBeforeCount_background_at_self

lemma; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:27)

```lean
lemma clockBeforeCount_background_at_self {n : ℕ}
    (clocks : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    clockBeforeCount (fun j => clocks (i.succAbove j)) (clocks i) =
      clockBeforeCount clocks (clocks i)
```

### measurableSet_beforeRank

lemma; [source line 34](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:34)

```lean
lemma measurableSet_beforeRank {n : ℕ} (i : Fin n) (k : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ | clockBeforeCount clocks (clocks i) = k}
```

### measurableSet_beforeCount

lemma; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:40)

```lean
lemma measurableSet_beforeCount {n : ℕ} (t : ℝ) (k : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ | clockBeforeCount clocks t = k}
```

### beforeRank_probability_integral

theorem; [source line 47](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:47)

Exact density of the event that label `i` has zero-based rank `k`.

```lean
theorem beforeRank_probability_integral {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (k : ℕ) :
    exponentialRace w {clocks | clockBeforeCount clocks (clocks i) = k} =
      ∫⁻ t, exponentialPDF (w.rate i) t *
        backgroundRace w i {background | clockBeforeCount background t = k}
```

### survivingAtRankProbability

def; [source line 71](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:71)

Probability that label `i` is still present while exactly `k` clocks
have arrived. The weak survival inequality complements the strict count.

```lean
def survivingAtRankProbability {n : ℕ} (w : Weights n) (i : Fin n) (k : ℕ)
    (t : ℝ) : ℝ≥0∞ :=
  exponentialRace w {clocks | t ≤ clocks i ∧ clockBeforeCount clocks t = k}
```

### measurable_survivingAtRankProbability

lemma; [source line 75](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:75)

```lean
lemma measurable_survivingAtRankProbability {n : ℕ} (w : Weights n)
    (i : Fin n) (k : ℕ) : Measurable (survivingAtRankProbability w i k)
```

### survivingAtRankProbability_eq

theorem; [source line 90](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:90)

Independence factors survival of the candidate and the deleted count.
This uses the actual product race, not an assumed hazard process.

```lean
theorem survivingAtRankProbability_eq {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (k : ℕ) (t : ℝ) :
    survivingAtRankProbability w i k t = expMeasure (w.rate i) (Ici t) *
      backgroundRace w i {background | clockBeforeCount background t = k}
```

### beforeRank_probability_eq_intensity

theorem; [source line 117](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:117)

The candidate's rank probability is its integrated crossing intensity,
expressed using the full race on both sides.

```lean
theorem beforeRank_probability_eq_intensity {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (k : ℕ) :
    exponentialRace w {clocks | clockBeforeCount clocks (clocks i) = k} =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (w.rate i) * survivingAtRankProbability w i k t
```

### sum_beforeRank_probability

theorem; [source line 139](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:139)

Every rank has exactly one preimage, almost surely; hence the sum of
candidate rank probabilities is exactly one.

```lean
theorem sum_beforeRank_probability {n : ℕ} (w : Weights n) (k : ℕ) (hk : k < n) :
    (∑ i, exponentialRace w {clocks | clockBeforeCount clocks (clocks i) = k}) = 1
```

### integrated_rank_crossing_intensity

theorem; [source line 160](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:160)

Integrated crossing intensity at any existing rank is exactly one.
This is the rigorous hazard normalization behind the spacing estimate.

```lean
theorem integrated_rank_crossing_intensity {n : ℕ} (w : Weights (n + 1))
    (k : ℕ) (hk : k < n + 1) :
    (∫⁻ t in Ioi 0, ∑ i, ENNReal.ofReal (w.rate i) *
      survivingAtRankProbability w i k t) = 1
```

### remaining_rate_lower_pointwise

lemma; [source line 173](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:173)

Deterministic reservoir input, at a single rank. The hypothesis is a
lower bound on the rate of every possible remaining label set, not an
assumed bound on a random spacing or its expectation.

```lean
lemma remaining_rate_lower_pointwise {n : ℕ} (w : Weights n) (k : ℕ) (B : ℝ)
    (hremaining : ∀ s : Finset (Fin n), s.card = n - k → B ≤ w.total s)
    (t : ℝ) (clocks : Fin n → ℝ) :
    ENNReal.ofReal B * (if clockBeforeCount clocks t = k then 1 else 0) ≤
      ∑ i, ENNReal.ofReal (w.rate i) *
        (if t ≤ clocks i ∧ clockBeforeCount clocks t = k then 1 else 0)
```

### beforeCount_probability_mul_le_intensity

theorem; [source line 197](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:197)

Integrating the deterministic rate bound over the actual race gives
the lower bound on its rank-crossing intensity.

```lean
theorem beforeCount_probability_mul_le_intensity {n : ℕ} (w : Weights n)
    (k : ℕ) (B : ℝ)
    (hremaining : ∀ s : Finset (Fin n), s.card = n - k → B ≤ w.total s) (t : ℝ) :
    ENNReal.ofReal B * exponentialRace w {clocks | clockBeforeCount clocks t = k} ≤
      ∑ i, ENNReal.ofReal (w.rate i) * survivingAtRankProbability w i k t
```

### beforeCount_occupation_le

theorem; [source line 234](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Occupation.lean:234)

Expected time spent with exactly `k` arrivals, obtained from the proved
crossing identity and a deterministic positive remaining-rate bound.

```lean
theorem beforeCount_occupation_le {n : ℕ} (w : Weights (n + 1))
    (k : ℕ) (hk : k < n + 1) (B : ℝ) (hB : 0 < B)
    (hremaining : ∀ s : Finset (Fin (n + 1)), s.card = (n + 1) - k → B ≤ w.total s) :
    (∫⁻ t in Ioi 0, exponentialRace w {clocks | clockBeforeCount clocks t = k}) ≤
      ENNReal.ofReal (1 / B)
```


## Luce/Section5PointCutoff.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5PointCutoff.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
```

### point_indicator_difference_le_count_difference

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5PointCutoff.lean:9)

```lean
theorem point_indicator_difference_le_count_difference {L : ℕ}
    (a b q : Fin L → ℕ) (hab : ∀ i, b i ≤ a i) :
    |(if a = q then (1 : ℝ) else 0) - (if b = q then 1 else 0)| ≤
      ∑ i, ((a i-b i : ℕ) : ℝ)
```

### cycle_point_indicator_cutoff_error

theorem; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section5PointCutoff.lean:32)

```lean
theorem cycle_point_indicator_cutoff_error (w : WeightArray) (L n : ℕ)
    (q : Fin L → ℕ) (α : ℝ) :
    |(∫ z, (if cycleCountVector L (raceRankPermutation z) = q then (1 : ℝ) else 0)
      ∂exponentialRace (w n)) -
      (∫ z, (if (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q
        then (1 : ℝ) else 0) ∂exponentialRace (w n))| ≤
      shortCycleTailExpectation w L n α
```

### EndpointShellAssumption.cycle_point_formula_tendsto

theorem; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section5PointCutoff.lean:55)

```lean
theorem EndpointShellAssumption.cycle_point_formula_tendsto
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) :
    Tendsto (fun α : ℝ => ∏ ell, Real.exp (-bulkCycleTraceIntensity f α ell.val) *
      bulkCycleTraceIntensity f α ell.val ^ q ell / ((q ell).factorial : ℝ))
      (𝓝[<] (1 : ℝ)) (𝓝 (∏ ell, Real.exp (-cycleTraceIntensity f ell.val) *
        cycleTraceIntensity f ell.val ^ q ell / ((q ell).factorial : ℝ)))
```


## Luce/Section5Predecessor.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Luce
```

### insertionPathWeight

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:21)

Product along an ordered source tuple ending at `v`.

```lean
def insertionPathWeight {α : Type*} {m : ℕ} (p : α → α → ℝ≥0∞)
    (v : α) (u : Fin m → α) : ℝ≥0∞ :=
  ∏ a, p (u a) ((Fin.snoc u v : Fin (m + 1) → α) a.succ)
```

### insertionPathSum

def; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:26)

Sum over all distinct-source paths, without a restriction on the endpoint.

```lean
def insertionPathSum {α : Type*} [Fintype α] [DecidableEq α] (p : α → α → ℝ≥0∞)
    (m : ℕ) (v : α) : ℝ≥0∞ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin m → α => Function.Injective u),
    insertionPathWeight p v u
```

### insertionPathWeight_cons

lemma; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:31)

```lean
lemma insertionPathWeight_cons {α : Type*} {m : ℕ} (p : α → α → ℝ≥0∞)
    (v k : α) (u : Fin m → α) :
    insertionPathWeight p v (Fin.cons k u) =
      p k ((Fin.snoc u v : Fin (m + 1) → α) 0) * insertionPathWeight p v u
```

### insertionPathSum_succ

lemma; [source line 41](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:41)

The new-label part of the predecessor sum is exactly the next path sum.
`Fin.consEquiv` proves the bijection and prevents any multiplicity loss.

```lean
lemma insertionPathSum_succ {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → α → ℝ≥0∞) (m : ℕ) (v : α) :
    insertionPathSum p (m + 1) v =
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → α => Function.Injective u),
        ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range u),
          p k ((Fin.snoc u v : Fin (m + 1) → α) 0) * insertionPathWeight p v u
```

### insertionColumn_le_new_add_length

lemma; [source line 71](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:71)

Splitting a column into new and repeated source labels. Nonnegativity is
provided by ENNReal and the repeated factors are bounded by `1`.

```lean
lemma insertionColumn_le_new_add_length {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (p : α → α → ℝ≥0∞) (hp : ∀ i j, p i j ≤ 1)
    (u : Fin m → α) (hu : Function.Injective u) (j : α) :
    (∑ k, p k j) ≤
      (∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range u), p k j) + m
```

### insertion_added_predecessor_le

theorem; [source line 95](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:95)

Deterministic added-predecessor estimate. The two terms explicitly
account for new predecessors and each of the `m` possible collisions.

```lean
theorem insertion_added_predecessor_le {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → α → ℝ≥0∞) (hp : ∀ i j, p i j ≤ 1) (m : ℕ) (v : α) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin m → α => Function.Injective u),
      (∑ k, p k ((Fin.snoc u v : Fin (m + 1) → α) 0)) *
        insertionPathWeight p v u) ≤
      insertionPathSum p (m + 1) v + m * insertionPathSum p m v
```

### ghostColumnKernel

def; [source line 116](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:116)

The paper's `c_j = ∑_k p_(k,j)`, with extended nonnegative values.

```lean
def ghostColumnKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (j : Fin n) : ℝ≥0∞ :=
  ∑ k, ghostOrderKernel w ell old k j
```

### ghostColumn

def; [source line 121](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:121)

The actual real column sum `c_j`, with the manuscript's orientation.

```lean
def ghostColumn {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ k, ghostEntry w ell old k j
```

### ghostPredecessorSum

def; [source line 127](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:127)

The precise source-restricted sum in `eq:added-predecessor`, with `m`
intermediate vertices. For `m=0`, its first target is the endpoint `v`.

```lean
def ghostPredecessorSum {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n =>
      Function.Injective u ∧ ∀ a, u a ≠ v),
    ghostColumnKernel w ell old ((Fin.snoc u v : Fin (m + 1) → Fin n) 0) *
      insertionPathWeight (ghostOrderKernel w ell old) v u
```

### ghostPredecessorSum_le

theorem; [source line 136](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:136)

The collision/new-label bound retains the original restriction in its
left side. Removing avoidance of `v` is explicitly justified by positivity.

```lean
theorem ghostPredecessorSum_le {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) :
    ghostPredecessorSum (m := m) w ell v old ≤
      ghostPathSum (m := m + 1) w ell v old + m * ghostPathSum (m := m) w ell v old
```

### predecessorConstant

def; [source line 154](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:154)

The explicit constant from the two cases of the source proof.

```lean
def predecessorConstant (ell m : ℕ) : ℕ :=
  (2 * (ell + (m + 1) + 2) + 1) ^ (m + 1) + m * (2 * (ell + m + 2) + 1) ^ m
```

### added_predecessor_ennreal

theorem; [source line 159](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:159)

The added-predecessor expectation, before conversion to real values.
Uniformity over n, all positive rates, and the endpoint is explicit.

```lean
theorem added_predecessor_ennreal {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) :
    (∫⁻ old, ghostPredecessorSum (m := m) w ell v old ∂exponentialRace w) ≤
      (predecessorConstant ell m : ℝ≥0∞)
```

### aemeasurable_ghostPredecessorSum

lemma; [source line 177](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:177)

```lean
lemma aemeasurable_ghostPredecessorSum {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    AEMeasurable (ghostPredecessorSum (m := m) w ell v) (exponentialRace w)
```

### ghostColumnKernel_ne_top

lemma; [source line 185](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:185)

```lean
lemma ghostColumnKernel_ne_top {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (j : Fin n) : ghostColumnKernel w ell old j ≠ ⊤
```

### ghostPredecessorSum_ne_top

lemma; [source line 191](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:191)

```lean
lemma ghostPredecessorSum_ne_top {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) : ghostPredecessorSum (m := m) w ell v old ≠ ⊤
```

### ghostColumnKernel_toReal

lemma; [source line 199](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:199)

```lean
lemma ghostColumnKernel_toReal {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (j : Fin n) :
    (ghostColumnKernel w ell old j).toReal = ghostColumn w ell old j
```

### ghostPredecessorSum_toReal

lemma; [source line 206](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:206)

```lean
lemma ghostPredecessorSum_toReal {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) :
    (ghostPredecessorSum (m := m) w ell v old).toReal =
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        ghostColumn w ell old ((Fin.snoc u v : Fin (m + 1) → Fin n) 0) *
          ∏ a, ghostEntry w ell old (u a)
            ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
```

### added_predecessor_integrable

theorem; [source line 224](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:224)

Integrability of the exact source expression, not an assumed expectation.

```lean
theorem added_predecessor_integrable {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) :
    Integrable (fun old =>
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        ghostColumn w ell old ((Fin.snoc u v : Fin (m + 1) → Fin n) 0) *
          ∏ a, ghostEntry w ell old (u a)
            ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)) (exponentialRace w)
```

### added_predecessor

theorem; [source line 240](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:240)

Equation (added-predecessor), with exactly the paper's column sums and
path products. Set ell=m+1 for its cycle-length convention.

```lean
theorem added_predecessor {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) :
    (∫ old,
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        ghostColumn w ell old ((Fin.snoc u v : Fin (m + 1) → Fin n) 0) *
          ∏ a, ghostEntry w ell old (u a)
            ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
      ∂exponentialRace w) ≤ (predecessorConstant ell m : ℝ)
```

### ghostPredecessorSum_zero

lemma; [source line 262](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:262)

The empty intermediate path is precisely the column sum at `v`, the
singleton-cycle convention required at source line 1150.

```lean
lemma ghostPredecessorSum_zero {n : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) :
    ghostPredecessorSum (m := 0) w ell v old = ghostColumnKernel w ell old v
```

### ghostColumn_integrable

theorem; [source line 267](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:267)

```lean
theorem ghostColumn_integrable {n : ℕ} (w : Weights n) (ell : ℕ) (v : Fin n) :
    Integrable (fun old => ghostColumn w ell old v) (exponentialRace w)
```

### ghostColumn_expectation_le

theorem; [source line 273](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Predecessor.lean:273)

The `ell=1` source interpretation is an actual finite bound for E c_v.

```lean
theorem ghostColumn_expectation_le {n : ℕ} (w : Weights n) (ell : ℕ) (v : Fin n) :
    (∫ old, ghostColumn w ell old v ∂exponentialRace w) ≤
      (2 * (ell + 1 + 2) + 1 : ℕ)
```


## Luce/Section5RaceConclusion.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RaceConclusion.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace Luce
```

### EndpointShellAssumption.cycle_vector_weak

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RaceConclusion.lean:9)

```lean
theorem EndpointShellAssumption.cycle_vector_weak
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (L : ℕ)
    (F : (Fin L → ℕ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, F (cycleCountVector L (raceRankPermutation z))
      ∂exponentialRace (w n)) atTop (𝓝 (∫ x, F x ∂cycleVectorPoissonLaw f L))
```


## Luce/Section5Resampling.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Resampling.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Luce
```

### pairedExponentialRace

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Resampling.lean:20)

Independent pairs `(E_i^0,E_i^1)`, with the rate attached to label `i`.

```lean
def pairedExponentialRace {n : ℕ} (w : Weights n) :
    Measure (Fin n → ℝ × ℝ) :=
  Measure.pi fun i => (expMeasure (w.rate i)).prod (expMeasure (w.rate i))
```

### instance at line 24

instance; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Resampling.lean:24)

```lean
instance pairedExponentialRace_isProbability {n : ℕ} (w : Weights n) :
    IsProbabilityMeasure (pairedExponentialRace w) := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  unfold pairedExponentialRace
  infer_instance
```

### swapClockCopies

def; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Resampling.lean:32)

Swap only the prescribed labels, keeping every rate attached to its label.

```lean
def swapClockCopies {n : ℕ} (s : Finset (Fin n))
    (c : Fin n → ℝ × ℝ) (i : Fin n) : ℝ × ℝ :=
  if i ∈ s then (c i).swap else c i
```

### swapClockCopies_involutive

theorem; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Resampling.lean:36)

```lean
theorem swapClockCopies_involutive {n : ℕ} (s : Finset (Fin n)) :
    Function.Involutive (swapClockCopies s)
```

### swapClockCopies_measurePreserving

theorem; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Resampling.lean:45)

The law-preserving swaps used in the finite insertion proof, source
1117–1123. This statement uses the actual exponential product law.

```lean
theorem swapClockCopies_measurePreserving {n : ℕ} (w : Weights n)
    (s : Finset (Fin n)) :
    MeasurePreserving (swapClockCopies s)
      (pairedExponentialRace w) (pairedExponentialRace w)
```

### pairedExponentialRace_background

theorem; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Resampling.lean:62)

The background projection is the original independent exponential race.

```lean
theorem pairedExponentialRace_background {n : ℕ} (w : Weights n) :
    MeasurePreserving (fun c : Fin n → ℝ × ℝ => fun i => (c i).1)
      (pairedExponentialRace w) (exponentialRace w)
```

### swapped_background_measurePreserving

theorem; [source line 70](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Resampling.lean:70)

Every fixed set of replacements again has the original race law.

```lean
theorem swapped_background_measurePreserving {n : ℕ} (w : Weights n)
    (s : Finset (Fin n)) :
    MeasurePreserving
      (fun c : Fin n → ℝ × ℝ => fun i => (swapClockCopies s c i).1)
      (pairedExponentialRace w) (exponentialRace w)
```

### swapped_background_injective_ae

theorem; [source line 79](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Resampling.lean:79)

The new background ranks form a permutation almost surely, for any
fixed replacement set. Distinctness is proved from the law, not assumed.

```lean
theorem swapped_background_injective_ae {n : ℕ} (w : Weights n)
    (s : Finset (Fin n)) :
    ∀ᵐ c ∂pairedExponentialRace w,
      Function.Injective (fun i => (swapClockCopies s c i).1)
```

### pairedExponentialRace_families

theorem; [source line 88](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Resampling.lean:88)

Actual joint law of the two entire clock families. This permits Tonelli
to interpret the window product as a conditional probability.

```lean
theorem pairedExponentialRace_families {n : ℕ} (w : Weights n) :
    MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
      (pairedExponentialRace w) ((exponentialRace w).prod (exponentialRace w))
```


## Luce/Section5Reservoir.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Reservoir.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace Luce
```

### moderateReservoir

def; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Reservoir.lean:20)

The labels of rate at least `d`, counted with their original labels.

```lean
def moderateReservoir (w : WeightArray) (n : ℕ) (d : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => d ≤ (w n).rate i)
```

### ProfileLimit.exists_large_superlevel

lemma; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Reservoir.lean:25)

Source lines 988–989: positive limiting rates have arbitrarily large
positive superlevel sets. All superlevel sets are measured on `(0,1)`.

```lean
lemma ProfileLimit.exists_large_superlevel {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {β : ℝ} (hβ : β < 1) :
    ∃ c : ℝ, 0 < c ∧ β < profileMeasure.real {x | c ≤ f x}
```

### stepProfile_superlevel_measure_le

lemma; [source line 62](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Reservoir.lean:62)

The actual step-profile cells give the required counting multiplicity:
each labelled clock occupies one cell of length `1/n`. This upper bound needs
only the finite-union inequality; no disjointness restriction is dropped in
the opposite direction.

```lean
lemma stepProfile_superlevel_measure_le (w : WeightArray) {n : ℕ} (hn : 0 < n)
    (d : ℝ) :
    profileMeasure.real {x | d ≤ stepProfile w n x} ≤
      ((moderateReservoir w n d).card : ℝ) / n
```

### ProfileLimit.moderate_reservoir

theorem; [source line 108](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Reservoir.lean:108)

Source lines 987–992: the bad portion of a positive superlevel set is
controlled by the `L¹` error, and hence the reservoir contains linearly many
labels. The source allows every real `α < 1`, including negative `α`.

```lean
theorem ProfileLimit.moderate_reservoir {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ∃ d η : ℝ, 0 < d ∧ 0 < η ∧
      ∀ᶠ n : ℕ in atTop,
        (α + 2 * η) * (n : ℝ) ≤ ((moderateReservoir w n d).card : ℝ)
```

### remaining_rate_of_reservoir

lemma; [source line 153](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Reservoir.lean:153)

The finite counting step in source lines 992–994. `removed` includes
both deleted clocks and arrivals. Its arbitrary form makes the claimed
uniformity over all deletion/arrival configurations explicit.

```lean
lemma remaining_rate_of_reservoir (w : WeightArray) (n : ℕ)
    {α d η : ℝ} (hd : 0 ≤ d) (m : ℕ)
    (hcount : (α + 2 * η) * (n : ℝ) ≤ ((moderateReservoir w n d).card : ℝ))
    (hm : (m : ℝ) ≤ η * n) (removed : Finset (Fin n))
    (hremoved : (removed.card : ℝ) ≤ α * n + m) :
    d * η * n ≤ ∑ i ∈ Finset.univ \ removed, (w n).rate i
```

### ProfileLimit.moderate_reservoir_with_remaining_rate

theorem; [source line 184](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Reservoir.lean:184)

The full moderate-reservoir lemma, including its consequence after a
fixed number `m` of deletions and at most `α n` arrivals. The same constants
work for every fixed `m`; only the sufficiently-large-row threshold changes.

```lean
theorem ProfileLimit.moderate_reservoir_with_remaining_rate
    {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f)
    {α : ℝ} (hα : α < 1) :
    ∃ d η : ℝ, 0 < d ∧ 0 < η ∧
      (∀ᶠ n : ℕ in atTop,
        (α + 2 * η) * (n : ℝ) ≤ ((moderateReservoir w n d).card : ℝ)) ∧
      ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, ∀ removed : Finset (Fin n),
        (removed.card : ℝ) ≤ α * n + m →
          d * η * n ≤ ∑ i ∈ Finset.univ \ removed, (w n).rate i
```

### section5UnitWeights_assumptions

theorem; [source line 207](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Reservoir.lean:207)

An explicit array satisfies all standing finite-mean hypotheses. Thus
the hypotheses used here, and the source's additional endpoint condition,
are jointly consistent. This is the manuscript's uniform-permutation example.

```lean
theorem section5UnitWeights_assumptions :
    NormalizedWeights section3UnitWeights ∧
      ProfileLimit section3UnitWeights (fun _ => 1) ∧
      EndpointAssumption section3UnitWeights
```


## Luce/Section5RetainedExpectation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedExpectation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace Luce
```

### retainedDeepCycleCount

def; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedExpectation.lean:11)

Actual cycles retained in S whose unique maximum lies in the deep
shell region. This auxiliary count uses the established maximum-root bijection.

```lean
def retainedDeepCycleCount {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (S : Finset (Fin n)) (J : ℕ) : ℕ :=
  ((deepShellLabels n J).filter (fun v => v ∈ Section5.maximumCycleRoots R k ∧
    (Function.periodicOrbit (R : Fin n → Fin n) v).toFinset ⊆ S)).card
```

### retainedDeepCycleCount_expectation

theorem; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedExpectation.lean:16)

```lean
theorem retainedDeepCycleCount_expectation {n : ℕ} (w : Weights n)
    (k J : ℕ) (S : Finset (Fin n)) :
    (∫ e, (retainedDeepCycleCount (raceRankPermutation e) k S J : ℝ) ∂exponentialRace w) =
      ∑ v ∈ deepShellLabels n J, (exponentialRace w).real (retainedMaximumCycleEvent k S v)
```

### EndpointShellAssumption.retained_expectation_tightness

theorem; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedExpectation.lean:38)

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


## Luce/Section5RetainedLabels.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedLabels.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Filter
namespace Luce
```

### retainedCycleLabels

def; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedLabels.lean:12)

The manuscript's two finite truncations: discard high rates globally
and low rates only in the fixed interior. This is a label set, not a new
restriction on WeightArray.

```lean
def retainedCycleLabels {n : ℕ} (w : Weights n) (M β δ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun u => w.rate u ≤ M ∧ ((u.val : ℝ)+1 ≤ β*n → δ ≤ w.rate u))
```

### retainedInteriorLabels

def; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedLabels.lean:15)

```lean
def retainedInteriorLabels {n : ℕ} (w : Weights n) (M β δ : ℝ) : Finset (Fin n) :=
  (retainedCycleLabels w M β δ).filter (fun u => (u.val : ℝ)+1 ≤ β*n)
```

### not_mem_retainedCycleLabels

theorem; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedLabels.lean:18)

```lean
theorem not_mem_retainedCycleLabels {n : ℕ} (w : Weights n) (M β δ : ℝ) (u : Fin n) :
    u ∉ retainedCycleLabels w M β δ ↔
      M < w.rate u ∨ (w.rate u < δ ∧ (u.val : ℝ)+1 ≤ β*n)
```

### retainedInteriorLabels_rate

theorem; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedLabels.lean:25)

```lean
theorem retainedInteriorLabels_rate {n : ℕ} (w : Weights n) (M β δ : ℝ)
    {u : Fin n} (hu : u ∈ retainedInteriorLabels w M β δ) : δ ≤ w.rate u
```

### eventually_retained_labels_cover

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedLabels.lean:30)

```lean
theorem eventually_retained_labels_cover (w : WeightArray) (M δ : ℝ) (J₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ u ∈ retainedCycleLabels (w n) M
        (1 - Real.exp (-(J₀ : ℝ))/2) δ,
      u ∈ retainedInteriorLabels (w n) M (1 - Real.exp (-(J₀ : ℝ))/2) δ ∨
        J₀ ≤ terminalShellNumber u
```


## Luce/Section5RetainedProbabilityBound.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedProbabilityBound.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### retained_deep_probability_bound

theorem; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedProbabilityBound.lean:13)

The actual retained maximum-cycle probability sum has the manuscript's
early-shell plus late-source/interior bound. Local cutoff premises are
explicit and are not promoted to assumptions of the frozen main theorem.

```lean
theorem retained_deep_probability_bound (w : WeightArray) (n J₀ J k : ℕ)
    (S S₀ : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ) (hJ₀ : 1 ≤ J₀) (hJ : 1 ≤ J)
    (hcut : 1 ≤ δ*((J : ℝ) - Real.sqrt J))
    (hrate : ∀ u ∈ S₀, δ ≤ (w n).rate u)
    (hcover : ∀ u ∈ S, u ∈ S₀ ∨ J₀ ≤ terminalShellNumber u)
    (hfloor : ∀ r ∈ Finset.Icc J₀ n, ∀ hs : (terminalShell n r).Nonempty,
      1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :
    (∑ v ∈ deepShellLabels n J,
      (exponentialRace (w n)).real (retainedMaximumCycleEvent (k+1) S v)) ≤
    (∑ j ∈ Finset.Icc J n, ∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostKernel (w n) (k+2) old u v ((j : ℝ) - Real.sqrt j) *
        markedReturnWeight (ghostEntry (w n) (k+2) old) k v u ∂exponentialRace (w n)) +
      (2*(k+2)+1 : ℕ)^(k+2) *
        (Real.exp (-δ*((J : ℝ) - Real.sqrt J)) +
          ∑ r ∈ Finset.Icc J₀ n, if hs : (terminalShell n r).Nonempty then
            Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0)
```


## Luce/Section5RetainedTightness.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedTightness.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Luce
```

### EndpointShellAssumption.retained_maximum_tightness

theorem; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section5RetainedTightness.lean:16)

Retained maximum-cycle tightness with the manuscript's cutoff order.
The source cutoff precedes the fixed interior low-rate cutoff, which
precedes the target cutoff and the eventual row. All finite helper premises
are discharged from normalization, the raw shell condition, and the literal
retained label set. This does not yet count the discarded cycles.

```lean
theorem EndpointShellAssumption.retained_maximum_tightness {w : WeightArray}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J₀ : ℕ, 2 ≤ J₀ ∧ ∀ M δ : ℝ, 0 < δ →
      ∃ J : ℕ, J₀ ≤ J ∧ ∀ᶠ n : ℕ in atTop,
        (∑ v ∈ deepShellLabels n J, (exponentialRace (w n)).real
          (retainedMaximumCycleEvent (k+1)
            (retainedCycleLabels (w n) M (1 - Real.exp (-(J₀ : ℝ))/2) δ) v)) < ε
```


## Luce/Section5ShellContract.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellContract.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Luce MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction ENNReal
universe u
namespace ShellMigrationContract
```

### section5

def; [source line 11](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellContract.lean:11)

```lean
def section5 : Prop :=
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
    (∀ k : ℕ, Integrable (cycleTraceIntegrand f k) (cyclicProfileMeasure (k+1)) ∧
      0 ≤ cycleTraceIntensity f k) ∧
    ∀ L : ℕ,
      (∀ F : (Fin L → ℕ) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, F (cycleCountVector L (π n ω)) ∂P n) atTop
          (𝓝 (∫ z, F z ∂cycleVectorPoissonLaw f L))) ∧
      Tendsto (fun n => cycleVectorTotalVariation
        ((P n).map (fun ω => cycleCountVector L (π n ω))) (cycleVectorPoissonLaw f L))
        atTop (𝓝 0)
```


## Luce/Section5ShellContractCheck.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellContractCheck.lean)

### section5_contractCheck

theorem; [source line 4](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellContractCheck.lean:4)

```lean
theorem section5_contractCheck : ShellMigrationContract.section5
```


## Luce/Section5ShellCutoff.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellCutoff.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
namespace Luce
```

### terminalShellNumber

def; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellCutoff.lean:9)

The unique logarithmic shell number, also defined for the interior
shell zero. It does not change the manuscript's positive-shell convention.

```lean
def terminalShellNumber {n : ℕ} (v : Fin n) : ℕ :=
  ⌊Real.log ((n : ℝ) / (terminalDepth v : ℝ))⌋₊
```

### terminalShellTime

def; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellCutoff.lean:12)

```lean
def terminalShellTime {n : ℕ} (v : Fin n) : ℝ :=
  (terminalShellNumber v : ℝ) - Real.sqrt (terminalShellNumber v)
```

### terminalShellNumber_eq_of_mem

theorem; [source line 15](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellCutoff.lean:15)

```lean
theorem terminalShellNumber_eq_of_mem {n j : ℕ} {v : Fin n}
    (hv : v ∈ terminalShell n j) : terminalShellNumber v = j
```

### mem_terminalShellNumber

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellCutoff.lean:20)

```lean
theorem mem_terminalShellNumber {n : ℕ} (v : Fin n) (hv : 1 ≤ terminalShellNumber v) :
    v ∈ terminalShell n (terminalShellNumber v)
```

### source_shell_time_le_target

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellCutoff.lean:28)

```lean
theorem source_shell_time_le_target {n r : ℕ} {u v : Fin n}
    (hu : u ∈ terminalShell n r) (hv : 1 ≤ terminalShellNumber v) (huv : u < v) :
    (r : ℝ) - Real.sqrt r ≤ terminalShellTime v
```

### cutoff_le_terminalShellTime

theorem; [source line 33](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellCutoff.lean:33)

```lean
theorem cutoff_le_terminalShellTime {n J : ℕ} {v : Fin n}
    (hJ : 1 ≤ J) (hv : J ≤ terminalShellNumber v) :
    (J : ℝ) - Real.sqrt J ≤ terminalShellTime v
```


## Luce/Section5ShellMain.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellMain.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace Luce
```

### section5_main_general

theorem; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellMain.lean:10)

The complete revised Section 5 conclusion on every realization of the
finite Luce law, with exactly the manuscript's model assumptions.

```lean
theorem section5_main_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    (∀ k : ℕ, Integrable (cycleTraceIntegrand f k) (cyclicProfileMeasure (k+1)) ∧
      0 ≤ cycleTraceIntensity f k) ∧
    ∀ L : ℕ,
      (∀ F : (Fin L → ℕ) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, F (cycleCountVector L (π n ω)) ∂P n) atTop
          (𝓝 (∫ z, F z ∂cycleVectorPoissonLaw f L))) ∧
      Tendsto (fun n => cycleVectorTotalVariation
        ((P n).map (fun ω => cycleCountVector L (π n ω))) (cycleVectorPoissonLaw f L))
        atTop (𝓝 0)
```


## Luce/Section5ShellMarkedEdge.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellMarkedEdge.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open scoped BigOperators
namespace Luce
```

### markedReturnWeight

def; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellMarkedEdge.lean:10)

Unrestricted return paths with k intermediate labels and fixed end u.
At k=0 this is the single edge from v to u.

```lean
def markedReturnWeight {α : Type*} [Fintype α] (p : α → α → ℝ)
    (k : ℕ) (v u : α) : ℝ :=
  ∑ t : Fin k → α, forwardPathWeight p v (Fin.snoc t u)
```

### markedReturnWeight_nonneg

theorem; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellMarkedEdge.lean:14)

```lean
theorem markedReturnWeight_nonneg {α : Type*} [Fintype α] (p : α → α → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (k : ℕ) (v u : α) :
    0 ≤ markedReturnWeight p k v u
```

### markedReturnWeight_sum_le

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellMarkedEdge.lean:19)

```lean
theorem markedReturnWeight_sum_le {α : Type*} [Fintype α] (p : α → α → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, p i j ≤ C) (k : ℕ) (v : α) :
    (∑ u, markedReturnWeight p k v u) ≤ C^(k+1)
```

### ghost_marked_edge_bound

theorem; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellMarkedEdge.lean:36)

The manuscript's marked-edge estimate for the actual common ghost
background. Its scalar envelope is a local helper premise, to be discharged
separately on late source shells and on the retained interior labels.

```lean
theorem ghost_marked_edge_bound {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S : Finset (Fin n)) (t d : ℝ) (hd : 0 ≤ d)
    (henvelope : ∀ u ∈ S, w.rate u * Real.exp (-w.rate u*t) ≤ d) :
    (∑ v ∈ Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t),
      ∑ u ∈ S, w.rate u * Real.exp (-w.rate u*t) *
        markedReturnWeight (ghostEntry w ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) * d
```


## Luce/Section5SieveRemainder.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SieveRemainder.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
```

### countSieveRemainder

def; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SieveRemainder.lean:8)

```lean
def countSieveRemainder {L : ℕ} (q : Fin L → ℕ) (K : ℕ) (x : Fin L → ℕ) : ℝ :=
  (∏ ell, (1 + ((x ell).descFactorial (q ell+(K+1)) : ℝ) /
    (((q ell).factorial : ℝ) * ((K+1).factorial : ℝ)))) - 1
```

### limitingSieveRemainder

def; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SieveRemainder.lean:12)

```lean
def limitingSieveRemainder {L : ℕ} (q : Fin L → ℕ) (K : ℕ) (rates : Fin L → ℝ) : ℝ :=
  (∏ ell, (1 + rates ell ^ (q ell+(K+1)) /
    (((q ell).factorial : ℝ) * ((K+1).factorial : ℝ)))) - 1
```

### bulk_sieve_remainder_limit

theorem; [source line 16](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SieveRemainder.lean:16)

```lean
theorem bulk_sieve_remainder_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L K : ℕ) (q : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z, countSieveRemainder q K
      (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val)
      ∂exponentialRace (w n)) atTop
      (𝓝 (limitingSieveRemainder q K (fun ell => bulkCycleTraceIntensity f α ell.val)))
```

### bulk_sieve_error_integral_le

theorem; [source line 47](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SieveRemainder.lean:47)

```lean
theorem bulk_sieve_error_integral_le {n : ℕ} (w : Weights n)
    (L K : ℕ) (q : Fin L → ℕ) (α : ℝ) :
    |(∫ z, countVectorSieve q K (fun ell =>
        Section5.bulkCycleCount (raceRankPermutation z) α ell.val) ∂exponentialRace w) -
      (∫ z, (if (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q
        then (1 : ℝ) else 0) ∂exponentialRace w)| ≤
      ∫ z, countSieveRemainder q K (fun ell =>
        Section5.bulkCycleCount (raceRankPermutation z) α ell.val) ∂exponentialRace w
```


## Luce/Section5SieveSeries.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SieveSeries.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Filter
open scoped BigOperators Topology
namespace Luce
```

### factorial_remainder_tendsto_zero

theorem; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SieveSeries.lean:8)

```lean
theorem factorial_remainder_tendsto_zero (a : ℝ) (q : ℕ) :
    Tendsto (fun K : ℕ => a ^ (q+(K+1)) /
      ((q.factorial : ℝ) * ((K+1).factorial : ℝ))) atTop (𝓝 0)
```

### limitingSieveRemainder_tendsto_zero

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SieveSeries.lean:19)

```lean
theorem limitingSieveRemainder_tendsto_zero {L : ℕ} (q : Fin L → ℕ)
    (rates : Fin L → ℝ) :
    Tendsto (fun K => limitingSieveRemainder q K rates) atTop (𝓝 0)
```

### count_sieve_series_limit

theorem; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SieveSeries.lean:26)

```lean
theorem count_sieve_series_limit (a : ℝ) (q : ℕ) :
    Tendsto (fun K : ℕ => ∑ j : Fin (K+1),
      (-1 : ℝ)^j.val * a^(q+j.val) / ((q.factorial : ℝ) * (j.val.factorial : ℝ))) atTop
      (𝓝 (Real.exp (-a) * a^q / (q.factorial : ℝ)))
```

### count_vector_sieve_series_limit

theorem; [source line 45](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SieveSeries.lean:45)

```lean
theorem count_vector_sieve_series_limit {L : ℕ} (q : Fin L → ℕ)
    (rates : Fin L → ℝ) :
    Tendsto (fun K : ℕ => ∏ ell, ∑ j : Fin (K+1),
      (-1 : ℝ)^j.val * rates ell ^ (q ell+j.val) /
        (((q ell).factorial : ℝ) * (j.val.factorial : ℝ))) atTop
      (𝓝 (∏ ell, Real.exp (-rates ell) * rates ell ^ q ell / ((q ell).factorial : ℝ)))
```


## Luce/Section5SingletonTail.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SingletonTail.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Function Filter
namespace Luce
```

### singleton_cycle_tail_le_fixed

theorem; [source line 8](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SingletonTail.lean:8)

```lean
theorem singleton_cycle_tail_le_fixed {n : ℕ} (e : Fin n → ℝ)
    (hinj : Function.Injective e) (α : ℝ) :
    Section5.cycleCount (raceRankPermutation e) 0 -
      Section5.bulkCycleCount (raceRankPermutation e) α 0 ≤ tailFixedPointCount e α
```

### cycleTailExpectation_zero_le

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SingletonTail.lean:30)

```lean
theorem cycleTailExpectation_zero_le (w : WeightArray) (n : ℕ) (α : ℝ) :
    cycleTailExpectation w 0 n α ≤
      ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace (w n)
```

### EndpointShellAssumption.cycle_tail_small

theorem; [source line 39](D:/princeton/Research/Lean/Lean_luce/Luce/Section5SingletonTail.lean:39)

```lean
theorem EndpointShellAssumption.cycle_tail_small {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, α < 1 ∧ ∀ᶠ n : ℕ in atTop, cycleTailExpectation w k n α < ε
```


## Luce/Section5TailExpectationBound.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5TailExpectationBound.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
```

### tail_cycle_expectation_le_retained_and_truncations

theorem; [source line 12](D:/princeton/Research/Lean/Lean_luce/Luce/Section5TailExpectationBound.lean:12)

```lean
theorem tail_cycle_expectation_le_retained_and_truncations (w : WeightArray)
    (n k J : ℕ) (M β δ α : ℝ)
    (hdeep : ∀ v : Fin n, α*n < (v.val : ℝ)+1 → J ≤ terminalShellNumber v) :
    (∫ e, ((Section5.cycleCount (raceRankPermutation e) k -
      Section5.bulkCycleCount (raceRankPermutation e) α k : ℕ) : ℝ)
      ∂exponentialRace (w n)) ≤
    (∫ e, (retainedDeepCycleCount (raceRankPermutation e) k
      (retainedCycleLabels (w n) M β δ) J : ℝ) ∂exponentialRace (w n)) +
    (k+1 : ℕ) * (highCycleExpectation w (k+1) n M +
      interiorLowCycleExpectation w (k+1) n β δ)
```


## Luce/Section5VectorTotalVariation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VectorTotalVariation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce
```

### raceCycleVectorLaw

def; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VectorTotalVariation.lean:9)

```lean
def raceCycleVectorLaw {n : ℕ} (w : Weights n) (L : ℕ) : ProbabilityMeasure (Fin L → ℕ) :=
  ⟨(exponentialRace w).map (fun z => cycleCountVector L (raceRankPermutation z)),
    (exponentialRace w).isProbabilityMeasure_map
      (measurable_race_permutation_statistic (cycleCountVector L)).aemeasurable⟩
```

### cycleVectorPoissonProbability

def; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VectorTotalVariation.lean:14)

```lean
def cycleVectorPoissonProbability (f : ℝ → ℝ) (L : ℕ) : ProbabilityMeasure (Fin L → ℕ) :=
  ⟨cycleVectorPoissonLaw f L, inferInstance⟩
```

### cycleVectorTotalVariation_eq_countable

theorem; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VectorTotalVariation.lean:19)

The generic countable-space TV is exactly the frozen contract's
supremum over event differences, with no change of convention.

```lean
theorem cycleVectorTotalVariation_eq_countable {L : ℕ}
    (μ ν : ProbabilityMeasure (Fin L → ℕ)) :
    cycleVectorTotalVariation (μ : Measure (Fin L → ℕ)) (ν : Measure (Fin L → ℕ)) =
      CountableLaw.probabilityTotalVariation μ ν
```

### raceCycleVectorLaw_real_singleton

theorem; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VectorTotalVariation.lean:32)

```lean
theorem raceCycleVectorLaw_real_singleton {n : ℕ} (w : Weights n) (L : ℕ)
    (q : Fin L → ℕ) :
    (raceCycleVectorLaw w L : Measure (Fin L → ℕ)).real {q} =
      (exponentialRace w).real {z | cycleCountVector L (raceRankPermutation z) = q}
```

### EndpointShellAssumption.cycle_vector_totalVariation

theorem; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VectorTotalVariation.lean:44)

Full cycle-count vector convergence in the exact total-variation
convention of the frozen contract.

```lean
theorem EndpointShellAssumption.cycle_vector_totalVariation
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (L : ℕ) :
    Tendsto (fun n => cycleVectorTotalVariation
      ((exponentialRace (w n)).map (fun z => cycleCountVector L (raceRankPermutation z)))
      (cycleVectorPoissonLaw f L)) atTop (𝓝 0)
```


## Luce/Section5VertexCount.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators
namespace Luce
```

### shortCycleVertexCount

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:22)

The number of vertices in `S` whose permutation cycle has length at
most `L`. Lengths are indexed by `Fin L` with the source's one-based shift.

```lean
def shortCycleVertexCount {n : ℕ} (R : Equiv.Perm (Fin n)) (L : ℕ)
    (S : Finset (Fin n)) : ℕ :=
  (S.filter fun v => ∃ k : Fin L, minimalPeriod (R : Fin n → Fin n) v = k.val + 1).card
```

### shortCycleVertexCount_eq_filter_period_le

theorem; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:28)

The `Fin L` representation is exactly the source condition that the
actual cycle length is at most `L`; finite permutations have positive period.

```lean
theorem shortCycleVertexCount_eq_filter_period_le {n : ℕ}
    (R : Equiv.Perm (Fin n)) (L : ℕ) (S : Finset (Fin n)) :
    shortCycleVertexCount R L S =
      (S.filter fun v => minimalPeriod (R : Fin n → Fin n) v ≤ L).card
```

### shortCycleVertexCount_inverse

theorem; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:48)

Passing between draw order and rank order leaves every counted vertex
unchanged; this uses the proved equality of the two minimal periods.

```lean
theorem shortCycleVertexCount_inverse {n : ℕ}
    (R : Equiv.Perm (Fin n)) (L : ℕ) (S : Finset (Fin n)) :
    shortCycleVertexCount R.symm L S = shortCycleVertexCount R L S
```

### shortCycleVertexCount_le_card

lemma; [source line 53](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:53)

```lean
lemma shortCycleVertexCount_le_card {n : ℕ} (R : Equiv.Perm (Fin n)) (L : ℕ)
    (S : Finset (Fin n)) : shortCycleVertexCount R L S ≤ S.card
```

### shortCycleVertexCount_zero

lemma; [source line 57](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:57)

```lean
lemma shortCycleVertexCount_zero {n : ℕ} (R : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : shortCycleVertexCount R 0 S = 0
```

### shortCycleVertexCount_empty

lemma; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:61)

```lean
lemma shortCycleVertexCount_empty {n : ℕ} (R : Equiv.Perm (Fin n)) (L : ℕ) :
    shortCycleVertexCount R L ∅ = 0
```

### measurableSet_shortCycleVertex

lemma; [source line 64](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:64)

```lean
lemma measurableSet_shortCycleVertex {n : ℕ} (L : ℕ) (v : Fin n) :
    MeasurableSet {clocks : Fin n → ℝ | ∃ k : Fin L,
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k.val + 1}
```

### measurable_shortCycleVertexCount

theorem; [source line 71](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:71)

Measurability follows from a finite sum of measurable vertex indicators.

```lean
theorem measurable_shortCycleVertexCount {n : ℕ} (L : ℕ) (S : Finset (Fin n)) :
    Measurable (fun clocks : Fin n → ℝ =>
      shortCycleVertexCount (raceRankPermutation clocks) L S)
```

### shortCycleVertexCount_integrable

theorem; [source line 85](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:85)

```lean
theorem shortCycleVertexCount_integrable {n : ℕ} (w : Weights n)
    (L : ℕ) (S : Finset (Fin n)) :
    Integrable (fun clocks => (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ))
      (exponentialRace w)
```

### shortCycleVertexCount_expectation_eq

theorem; [source line 100](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:100)

Exact vertex counting: the expectation is the sum of short-cycle
membership probabilities, with no multiplicity or symmetry factor.

```lean
theorem shortCycleVertexCount_expectation_eq {n : ℕ} (w : Weights n)
    (L : ℕ) (S : Finset (Fin n)) :
    (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ)
      ∂exponentialRace w) =
      ∑ v ∈ S, (exponentialRace w).real {clocks | ∃ k : Fin L,
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k.val + 1}
```

### shortCycleVertexCount_expectation_le

theorem; [source line 127](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:127)

The finite union bound over lengths, for arbitrary `S` and `L`, used
to pass from the single-vertex cycle estimate to `V_(n,L)(S)`.

```lean
theorem shortCycleVertexCount_expectation_le {n : ℕ} (w : Weights n)
    (L : ℕ) (S : Finset (Fin n)) :
    (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ)
      ∂exponentialRace w) ≤
      ∑ v ∈ S, ∑ k : Fin L, (exponentialRace w).real {clocks |
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k.val + 1}
```

### shortCycleVertexCount_expectation_le_ghost

theorem; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section5VertexCount.lean:141)

Combining the previous count with the proved ghost cycle comparison.
Every individual integral is justified by `ghostCycleVertexSum_integrable`.

```lean
theorem shortCycleVertexCount_expectation_le_ghost {n : ℕ} (w : Weights n)
    (L : ℕ) (S : Finset (Fin n)) :
    (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ)
      ∂exponentialRace w) ≤
      ∑ v ∈ S, ∑ k : Fin L,
        ∫ old, ghostCycleVertexSum w k.val v old ∂exponentialRace w
```


## Luce/Section5WindowLength.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce
```

### ghostWindowVolume

def; [source line 23](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:23)

Lebesgue measure of the paper's open window `J_j`. The zero extension
at tied backgrounds is on a proved null set under the exponential race.

```lean
def ghostWindowVolume {n : ℕ} (ell : ℕ) (old : Fin n → ℝ) (j : Fin n) : ℝ≥0∞ :=
  if h : Function.Injective old then volume {t | GhostWindowByOrder old h ell j t} else 0
```

### ghostWindowLength

def; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:27)

Real length; finiteness is proved below before using its expectation.

```lean
def ghostWindowLength {n : ℕ} (ell : ℕ) (old : Fin n → ℝ) (j : Fin n) : ℝ :=
  (ghostWindowVolume ell old j).toReal
```

### ghostWindowVolume_eq_count

lemma; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:30)

```lean
lemma ghostWindowVolume_eq_count {n : ℕ} (ell : ℕ) (old : Fin n → ℝ)
    (hinj : Injective old) (hnonneg : ∀ i, 0 ≤ old i) (j : Fin n) :
    ghostWindowVolume ell old j = volume {t | GhostCountWindow ell old j t}
```

### measurable_ghostCountWindowVolume

lemma; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:40)

```lean
lemma measurable_ghostCountWindowVolume {n : ℕ} (ell : ℕ) (j : Fin n) :
    Measurable (fun old : Fin n → ℝ => volume {t | GhostCountWindow ell old j t})
```

### ghostWindowVolume_ae_eq_count

lemma; [source line 47](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:47)

```lean
lemma ghostWindowVolume_ae_eq_count {n : ℕ} (w : Weights n) (ell : ℕ) (j : Fin n) :
    (fun old => ghostWindowVolume ell old j) =ᵐ[exponentialRace w]
      (fun old => volume {t | GhostCountWindow ell old j t})
```

### aemeasurable_ghostWindowVolume

lemma; [source line 54](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:54)

```lean
lemma aemeasurable_ghostWindowVolume {n : ℕ} (w : Weights n) (ell : ℕ) (j : Fin n) :
    AEMeasurable (fun old => ghostWindowVolume ell old j) (exponentialRace w)
```

### ghostWindowVolume_expectation_eq

theorem; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:60)

Tonelli for the actual order-statistic interval.

```lean
theorem ghostWindowVolume_expectation_eq {n : ℕ} (w : Weights n) (ell : ℕ) (j : Fin n) :
    (∫⁻ old, ghostWindowVolume ell old j ∂exponentialRace w) =
      ∫⁻ t, exponentialRace w {old | GhostCountWindow ell old j t}
```

### measurable_beforeCount_probability

lemma; [source line 70](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:70)

```lean
lemma measurable_beforeCount_probability {n : ℕ} (w : Weights n) (k : ℕ) :
    Measurable (fun t : ℝ => exponentialRace w {old | clockBeforeCount old t = k})
```

### ghostCountWindow_probability_le_rank_sum

lemma; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:78)

Only ranks between the two window endpoints can be occupied.

```lean
lemma ghostCountWindow_probability_le_rank_sum {n : ℕ} (w : Weights n)
    (ell : ℕ) (j : Fin n) (t : ℝ) :
    exponentialRace w {old | GhostCountWindow ell old j t} ≤
      (Ioi 0).indicator (fun t => ∑ k ∈ Finset.Icc (j.val - ell) (j.val + ell),
        exponentialRace w {old | clockBeforeCount old t = k}) t
```

### ghostWindowVolume_expectation_le

theorem; [source line 103](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:103)

Finite interior-window estimate. All reservoir information appears in
`hremaining`; no conditional spacing law or expectation is a hypothesis.

```lean
theorem ghostWindowVolume_expectation_le {n : ℕ} (w : Weights (n + 1))
    (ell : ℕ) (j : Fin (n + 1)) (hj : j.val + ell < n + 1)
    (B : ℝ) (hB : 0 < B)
    (hremaining : ∀ k, k ≤ j.val + ell → ∀ s : Finset (Fin (n + 1)),
      s.card = (n + 1) - k → B ≤ w.total s) :
    (∫⁻ old, ghostWindowVolume ell old j ∂exponentialRace w) ≤
      ENNReal.ofReal ((2 * ell + 1 : ℕ) / B)
```

### ghostWindowLength_integrable

theorem; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:141)

The actual length is integrable; the preceding finite bound rules out
using totalized `toReal` to conceal infinite intervals.

```lean
theorem ghostWindowLength_integrable {n : ℕ} (w : Weights (n + 1))
    (ell : ℕ) (j : Fin (n + 1)) (hj : j.val + ell < n + 1)
    (B : ℝ) (hB : 0 < B)
    (hremaining : ∀ k, k ≤ j.val + ell → ∀ s : Finset (Fin (n + 1)),
      s.card = (n + 1) - k → B ≤ w.total s) :
    Integrable (fun old => ghostWindowLength ell old j) (exponentialRace w)
```

### ghostWindowLength_expectation_le

theorem; [source line 153](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowLength.lean:153)

Real-valued expected length of the paper's interval, with the exact
finite reservoir assumptions exposed.

```lean
theorem ghostWindowLength_expectation_le {n : ℕ} (w : Weights (n + 1))
    (ell : ℕ) (j : Fin (n + 1)) (hj : j.val + ell < n + 1)
    (B : ℝ) (hB : 0 < B)
    (hremaining : ∀ k, k ≤ j.val + ell → ∀ s : Finset (Fin (n + 1)),
      s.card = (n + 1) - k → B ≤ w.total s) :
    (∫ old, ghostWindowLength ell old j ∂exponentialRace w) ≤
      (2 * ell + 1 : ℕ) / B
```


## Luce/Section5WindowProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Luce
```

### GhostCountWindow

def; [source line 22](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:22)

Membership in the ghost window, expressed by the number of old clocks
strictly before the inserted time. The index `j` represents paper rank j+1.

```lean
def GhostCountWindow {n : ℕ} (ell : ℕ) (old : Fin n → ℝ)
    (j : Fin n) (t : ℝ) : Prop :=
  0 < t ∧ j.val + 1 ≤ clockBeforeCount old t + ell ∧
    clockBeforeCount old t < j.val + 1 + ell
```

### measurable_clockBeforeCount

lemma; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:27)

```lean
lemma measurable_clockBeforeCount {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (c : Ω → Fin n → ℝ) (t : Ω → ℝ)
    (hc : ∀ i, Measurable (fun x => c x i)) (ht : Measurable t) :
    Measurable (fun x => clockBeforeCount (c x) (t x))
```

### measurableSet_ghostCountWindow

lemma; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:40)

```lean
lemma measurableSet_ghostCountWindow {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ell : ℕ) (c : Ω → Fin n → ℝ) (j : Fin n) (t : Ω → ℝ)
    (hc : ∀ i, Measurable (fun x => c x i)) (ht : Measurable t) :
    MeasurableSet {x | GhostCountWindow ell (c x) j (t x)}
```

### GhostCountSuccess

def; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:50)

The endpoint `v` is appended, and need not be distinct from the sources.

```lean
def GhostCountSuccess {n m : ℕ} (ell : ℕ) (v : Fin n) (u : Fin m → Fin n)
    (c : Fin n → ℝ × ℝ) : Prop :=
  ∀ a, GhostCountWindow ell (fun i => (c i).1)
    ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) (c (u a)).2
```

### ApproximateClockPath

def; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:55)

```lean
def ApproximateClockPath {n m : ℕ} (q : ℕ) (v : Fin n) (u : Fin m → Fin n)
    (c : Fin n → ℝ) : Prop :=
  ∀ a, Nat.dist (clockBeforeCount c (c (u a)))
    ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ).val ≤ q
```

### measurableSet_ghostCountSuccess

lemma; [source line 60](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:60)

```lean
lemma measurableSet_ghostCountSuccess {n m : ℕ}
    (ell : ℕ) (v : Fin n) (u : Fin m → Fin n) :
    MeasurableSet {c | GhostCountSuccess ell v u c}
```

### measurableSet_approximateClockPath

lemma; [source line 70](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:70)

```lean
lemma measurableSet_approximateClockPath {n m : ℕ}
    (q : ℕ) (v : Fin n) (u : Fin m → Fin n) :
    MeasurableSet {c | ApproximateClockPath q v u c}
```

### ghostCountSuccess_implies_swapped_path

theorem; [source line 86](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:86)

Deterministic implication after the actual finite set of coordinate
swaps. The cardinality bound holds also when sources repeat; distinctness
is needed later for the conditional product formula, not for this step.

```lean
theorem ghostCountSuccess_implies_swapped_path {n m : ℕ}
    (ell : ℕ) (v : Fin n) (u : Fin m → Fin n) (c : Fin n → ℝ × ℝ)
    (hsuccess : GhostCountSuccess ell v u c) :
    ApproximateClockPath (ell + m + 2) v u
      (fun i => (swapClockCopies (Finset.univ.image u) c i).1)
```

### ghostCountSuccess_probability_le

theorem; [source line 114](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:114)

Each success event is compared with the same approximate-path event
under the original background law. This is the measure-preserving
comparison at source lines 1121–1136, not an assumed coupling.

```lean
theorem ghostCountSuccess_probability_le {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) (u : Fin m → Fin n) :
    pairedExponentialRace w {c | GhostCountSuccess ell v u c} ≤
      exponentialRace w {c | ApproximateClockPath (ell + m + 2) v u c}
```

### sum_measures_eq_lintegral_count

lemma; [source line 128](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:128)

Integrating a finite count is exactly the sum of its event probabilities;
this explicitly justifies the sum over all proposed source tuples.

```lean
lemma sum_measures_eq_lintegral_count {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (P : ι → Ω → Prop)
    (hP : ∀ i ∈ s, MeasurableSet {x | P i x}) :
    ∑ i ∈ s, μ {x | P i x} =
      ∫⁻ x, ((s.filter (fun i => P i x)).card : ℝ≥0∞) ∂μ
```

### sum_ghostCountSuccess_probability_le

theorem; [source line 152](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:152)

The expected number of successful distinct-source insertions, uniformly
over all rates and all terminal vertices. This proves the probabilistic
swap-and-count step, including its source-distinctness restriction.

```lean
theorem sum_ghostCountSuccess_probability_le {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
      pairedExponentialRace w {c | GhostCountSuccess ell v u c} ≤
        ((2 * (ell + m + 2) + 1) ^ m : ℕ)
```

### ghostCountKernel

def; [source line 182](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:182)

The conditional probability of inserting label i into rank-window j.

```lean
def ghostCountKernel {n : ℕ} (w : Weights n) (ell : ℕ) (old : Fin n → ℝ)
    (i j : Fin n) : ℝ≥0∞ :=
  expMeasure (w.rate i) {t | GhostCountWindow ell old j t}
```

### measurable_ghostCountKernel

lemma; [source line 186](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:186)

```lean
lemma measurable_ghostCountKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (i j : Fin n) : Measurable (fun old => ghostCountKernel w ell old i j)
```

### ghostCountKernel_product

theorem; [source line 197](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:197)

Distinct sources yield the product of their window probabilities.
Independence comes from the replacement race; windows share one background.

```lean
theorem ghostCountKernel_product {n m : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (v : Fin n) (u : Fin m → Fin n)
    (hu : Function.Injective u) :
    exponentialRace w {new | ∀ a, GhostCountWindow ell old
      ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) (new (u a))} =
        ∏ a, ghostCountKernel w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
```

### measurableSet_ghostFamilySuccess

lemma; [source line 223](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:223)

```lean
lemma measurableSet_ghostFamilySuccess {n m : ℕ}
    (ell : ℕ) (v : Fin n) (u : Fin m → Fin n) :
    MeasurableSet {c : (Fin n → ℝ) × (Fin n → ℝ) |
      ∀ a, GhostCountWindow ell c.1
        ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) (c.2 (u a))}
```

### lintegral_ghostCountKernel_product

theorem; [source line 237](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:237)

Tonelli and the actual independence of replacement clocks identify the
expectation of a window product with the successful-insertion probability.

```lean
theorem lintegral_ghostCountKernel_product {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) (u : Fin m → Fin n) (hu : Function.Injective u) :
    (∫⁻ old, ∏ a, ghostCountKernel w ell old (u a)
      ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) ∂exponentialRace w) =
      pairedExponentialRace w {c | GhostCountSuccess ell v u c}
```

### finite_insertion_path_countWindow

theorem; [source line 261](D:/princeton/Research/Lean/Lean_luce/Luce/Section5WindowProbability.lean:261)

The full expected distinct-source path-product bound for count windows.
There is no additional hypothesis encoding the probability comparison.
Source: Lemma 5.3, `eq:finite-insertion-path`, with its explicit constant.

```lean
theorem finite_insertion_path_countWindow {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    (∫⁻ old,
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, ghostCountKernel w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
      ∂exponentialRace w) ≤ ((2 * (ell + m + 2) + 1) ^ m : ℕ)
```


## Luce/Section4ShellContractCheck.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellContractCheck.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Luce MeasureTheory
open scoped ENNReal
```

### section4_contractCheck

theorem; [source line 10](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellContractCheck.lean:10)

This closed theorem has no external explicit, implicit, or instance
parameters. All allowed model data are quantified by the frozen contract.

```lean
theorem section4_contractCheck : ShellMigrationContract.section4
```

### Luce.Shell.fullIntensity_eq_uniform

theorem; [source line 20](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellContractCheck.lean:20)

The new constructor has exactly the same mathematical intensity as
the old constructor whenever the stronger uniform condition holds.

```lean
theorem Luce.Shell.fullIntensity_eq_uniform
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : UniformEndpointAssumption w) :
    Luce.Shell.fullIntensity w f hnorm hf hend.shell =
      Luce.fullIntensity w f hnorm hf hend
```


## Luce/Section4ShellContractRepresentation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellContractRepresentation.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open Luce MeasureTheory Set
namespace ShellMigrationContract
```

### old_fullIntensity_underlying

theorem; [source line 9](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellContractRepresentation.lean:9)

The intensity specified in the frozen conclusion is exactly the existing
one whenever that existing constructor is available. No limiting law is changed.

```lean
theorem old_fullIntensity_underlying (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (hend : UniformEndpointAssumption w) :
    (fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1)) =
      (interiorDensityMeasure f 1).map (projIcc 0 1 zero_le_one)
```


## Luce/Section4ShellMigrationContract.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellMigrationContract.lean)

Namespace / shared context (consult source for section boundaries):

```lean
noncomputable section
open Luce MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ENNReal
universe u
namespace ShellMigrationContract
```

### section4

def; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellMigrationContract.lean:18)

Closed arbitrary-space form of `thm:main-poisson`, source lines 318–332.
There are no ambient mathematical section variables or assumed instances.

```lean
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
```


## Luce/Section4ShellMigrationFoundations.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4ShellMigrationFoundations.lean)

No declarations; imports or audit commands only.


## Luce/Section2SpatialPoissonLaplace.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2SpatialPoissonLaplace.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction NNReal
namespace Luce
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
```

### totalPredictable_tendsto

theorem; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section2SpatialPoissonLaplace.lean:27)

The total predictable mass converges in probability by applying the
weak-measure hypothesis to the constant-one spatial test.

```lean
theorem totalPredictable_tendsto
    (hweak : WeakMeasureConvergesInProbability P
      (fun n => (B n).predictableMeasure (x n)) ν) :
    ConvergesInProbability P
      (fun n ω => ∑ k ∈ Finset.range n, (B n).toProcess.probability k ω)
      (ν.mass : ℝ)
```

### pointMeasure_laplace_tendsto

theorem; [source line 44](D:/princeton/Research/Lean/Lean_luce/Luce/Section2SpatialPoissonLaplace.lean:44)

Under the manuscript's weak predictable-measure and vanishing-maximum
hypotheses, each nonnegative continuous spatial Laplace test converges to
the corresponding test under the constructed finite Poisson law.

```lean
theorem pointMeasure_laplace_tendsto
    (hweak : WeakMeasureConvergesInProbability P
      (fun n => (B n).predictableMeasure (x n)) ν)
    (hmax : ConvergesInProbability P (fun n => (B n).toProcess.rowMaximum n) 0)
    (g : X →ᵇ ℝ≥0) :
    Tendsto (fun n => ∫ ω,
      pointLaplace (fun z => (g z : ℝ)) ((B n).pointMeasure (x n) ω) ∂P n)
      atTop (𝓝 (∫ s, pointLaplace (fun z => (g z : ℝ)) s ∂finitePoissonLaw ν))
```


## Luce/Section2Stopping.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open scoped BigOperators
open MeasureTheory
namespace Luce
section Measurability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
```

### stoppedMass

def; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:18)

Accumulated compensator after discarding terms that violate either cap.

```lean
noncomputable def stoppedMass (p : ℕ → ℝ) (δ K : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if p k ≤ δ ∧ stoppedMass p δ K k + p k ≤ K
    then stoppedMass p δ K k + p k else stoppedMass p δ K k
```

### keepTerm

def; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:24)

The predictable acceptance test before draw `k`.

```lean
def keepTerm (p : ℕ → ℝ) (δ K : ℝ) (k : ℕ) : Prop :=
  p k ≤ δ ∧ stoppedMass p δ K k + p k ≤ K
```

### stoppedProbability

def; [source line 28](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:28)

Conditional probability retained by the truncation.

```lean
noncomputable def stoppedProbability (p : ℕ → ℝ) (δ K : ℝ) (k : ℕ) : ℝ := by
  classical
  exact if keepTerm p δ K k then p k else 0
```

### stoppedMass_succ

lemma; [source line 32](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:32)

```lean
lemma stoppedMass_succ (p : ℕ → ℝ) (δ K : ℝ) (k : ℕ) :
    stoppedMass p δ K (k + 1) = stoppedMass p δ K k + stoppedProbability p δ K k
```

### stoppedProbability_nonneg

lemma; [source line 38](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:38)

```lean
lemma stoppedProbability_nonneg {p : ℕ → ℝ} {δ K : ℝ} {k : ℕ}
    (hp : 0 ≤ p k) : 0 ≤ stoppedProbability p δ K k
```

### stoppedProbability_le

lemma; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:43)

```lean
lemma stoppedProbability_le {p : ℕ → ℝ} {δ K : ℝ} {k : ℕ}
    (hp : 0 ≤ p k) : stoppedProbability p δ K k ≤ p k
```

### stoppedProbability_le_cap

lemma; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:48)

```lean
lemma stoppedProbability_le_cap (p : ℕ → ℝ) {δ K : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    stoppedProbability p δ K k ≤ δ
```

### stoppedMass_nonneg

lemma; [source line 55](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:55)

```lean
lemma stoppedMass_nonneg {p : ℕ → ℝ} {δ K : ℝ} (hp : ∀ k, 0 ≤ p k) (k : ℕ) :
    0 ≤ stoppedMass p δ K k
```

### stoppedMass_le_cap

lemma; [source line 61](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:61)

```lean
lemma stoppedMass_le_cap (p : ℕ → ℝ) {δ K : ℝ} (hK : 0 ≤ K) (k : ℕ) :
    stoppedMass p δ K k ≤ K
```

### sum_stoppedProbability

lemma; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:72)

The recursive accumulator is exactly the sum of retained probabilities.

```lean
lemma sum_stoppedProbability (p : ℕ → ℝ) (δ K : ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, stoppedProbability p δ K j) = stoppedMass p δ K k
```

### stoppedMass_le_sum

lemma; [source line 78](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:78)

```lean
lemma stoppedMass_le_sum {p : ℕ → ℝ} {δ K : ℝ} (hp : ∀ k, 0 ≤ p k) (k : ℕ) :
    stoppedMass p δ K k ≤ ∑ j ∈ Finset.range k, p j
```

### keepTerm_of_total_le

theorem; [source line 84](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:84)

On the good event for the original array, every test is accepted.

```lean
theorem keepTerm_of_total_le {p : ℕ → ℝ} {δ K : ℝ} {N : ℕ}
    (hp : ∀ k, 0 ≤ p k) (hcap : ∀ k < N, p k ≤ δ)
    (htotal : ∑ j ∈ Finset.range N, p j ≤ K) {k : ℕ} (hk : k < N) :
    keepTerm p δ K k
```

### stoppedProbability_eq_of_total_le

theorem; [source line 98](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:98)

```lean
theorem stoppedProbability_eq_of_total_le {p : ℕ → ℝ} {δ K : ℝ} {N : ℕ}
    (hp : ∀ k, 0 ≤ p k) (hcap : ∀ k < N, p k ≤ δ)
    (htotal : ∑ j ∈ Finset.range N, p j ≤ K) {k : ℕ} (hk : k < N) :
    stoppedProbability p δ K k = p k
```

### deletion_subset

theorem; [source line 106](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:106)

A deletion entails either an excessive original atom or excessive original
total mass; this is the event inclusion used to remove the truncation.

```lean
theorem deletion_subset {p : ℕ → ℝ} {δ K : ℝ} {N : ℕ}
    (hp : ∀ k, 0 ≤ p k) (hdelete : ∃ k < N, ¬keepTerm p δ K k) :
    (∃ k < N, δ < p k) ∨ K < ∑ j ∈ Finset.range N, p j
```

### measurable_stoppedMass

theorem; [source line 120](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:120)

The cap is predictable because it only uses the current predictable
probability and probabilities from earlier draws.

```lean
theorem measurable_stoppedMass (ℱ : Filtration ℕ mΩ) (p : ℕ → Ω → ℝ)
    (hp : ∀ k, Measurable[ℱ k] (p k)) (δ K : ℝ) :
    ∀ k, Measurable[ℱ k] (fun ω => stoppedMass (fun j => p j ω) δ K k)
```

### measurableSet_keepTerm

theorem; [source line 135](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:135)

```lean
theorem measurableSet_keepTerm (ℱ : Filtration ℕ mΩ) (p : ℕ → Ω → ℝ)
    (hp : ∀ k, Measurable[ℱ k] (p k)) (δ K : ℝ) (k : ℕ) :
    MeasurableSet[ℱ k] {ω | keepTerm (fun j => p j ω) δ K k}
```

### measurable_stoppedProbability

theorem; [source line 141](D:/princeton/Research/Lean/Lean_luce/Luce/Section2Stopping.lean:141)

```lean
theorem measurable_stoppedProbability (ℱ : Filtration ℕ mΩ) (p : ℕ → Ω → ℝ)
    (hp : ∀ k, Measurable[ℱ k] (p k)) (δ K : ℝ) (k : ℕ) :
    Measurable[ℱ k] (fun ω => stoppedProbability (fun j => p j ω) δ K k)
```


## Luce/Section4TailAssumptions.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailAssumptions.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
```

### NormalizedWeights.sum_rates_succ

lemma; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailAssumptions.lean:17)

```lean
lemma NormalizedWeights.sum_rates_succ {w : WeightArray} (hnorm : NormalizedWeights w)
    (n : ℕ) : ∑ i, (w (n + 1)).rate i = ((n + 1 : ℕ) : ℝ)
```

### EndpointAssumption.eventually_terminal_rates

lemma; [source line 27](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailAssumptions.lean:27)

The approved endpoint assumption supplies the rates required for the
rounded terminal counts in the existing epsilon estimate.

```lean
lemma EndpointAssumption.eventually_terminal_rates {w : WeightArray}
    (hend : EndpointAssumption w) :
    ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧
      ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε₀ * (n + 1)⌉₊,
        γ ≤ (w (n + 1)).rate (terminalCandidate n m)
```

### endpointAssumption_epsilon_estimate

theorem; [source line 57](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailAssumptions.lean:57)

Equation `eq:tail-epsilon`, derived from the approved normalization and
endpoint assumption without any profile hypothesis.

```lean
theorem endpointAssumption_epsilon_estimate (w : WeightArray)
    (hnorm : NormalizedWeights w) (hend : EndpointAssumption w) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        limsup (epsilonTailExpectation (fun n => w (n + 1)) ε) atTop ≤
          (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4)
```

### endpointAssumption_epsilon_estimate_bounded

theorem; [source line 69](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailAssumptions.lean:69)

The same epsilon estimate, retaining eventual boundedness of the
expectations. This makes later comparisons of real-valued limsups valid.

```lean
theorem endpointAssumption_epsilon_estimate_bounded (w : WeightArray)
    (hnorm : NormalizedWeights w) (hend : EndpointAssumption w) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        IsBoundedUnder (· ≤ ·) atTop (epsilonTailExpectation (fun n => w (n + 1)) ε) ∧
        limsup (epsilonTailExpectation (fun n => w (n + 1)) ε) atTop ≤
          (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4)
```


## Luce/Section4TailCount.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailCount.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Luce
```

### tailFixedPointCount

def; [source line 18](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailCount.lean:18)

The exact number of fixed-point atoms in `(α, 1]`.

```lean
noncomputable def tailFixedPointCount {n : ℕ}
    (e : Fin n → ℝ) (α : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun k : Fin n =>
    α * (n : ℝ) < (k.val : ℝ) + 1 ∧ rankOf e k = k.val + 1).card
```


## Luce/Section4TailCountIndex.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailCountIndex.lean)

Namespace / shared context (consult source for section boundaries):

```lean
namespace Luce
```

### rankOf_eq_raceRank_for_tail

lemma; [source line 13](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailCountIndex.lean:13)

```lean
lemma rankOf_eq_raceRank_for_tail {n : ℕ} (e : Fin n → ℝ) (k : Fin n) :
    rankOf e k = raceRank e k
```

### spatial_tail_iff_terminal_index

lemma; [source line 19](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailCountIndex.lean:19)

```lean
lemma spatial_tail_iff_terminal_index {n : ℕ} (k : Fin (n + 1)) (ε : ℝ) :
    (1 - ε) * ((n + 1 : ℕ) : ℝ) < (k.val : ℝ) + 1 ↔
      n + 1 - k.val ≤ ⌈ε * (n + 1)⌉₊
```

### tailFixedPointCount_eq_terminalFixedPointCount

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailCountIndex.lean:30)

The approved spatial count is exactly the terminal-index count, including
the ceiling when `ε * (n + 1)` is not an integer.

```lean
theorem tailFixedPointCount_eq_terminalFixedPointCount (n : ℕ)
    (e : Fin (n + 1) → ℝ) {ε : ℝ} (_hε : 0 < ε) (hεone : ε < 1) :
    tailFixedPointCount e (1 - ε) =
      terminalFixedPointCount (terminalCandidate n) ⌈ε * (n + 1)⌉₊ e
```


## Luce/Section4TailLimit.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailLimit.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open Filter
open scoped Topology
namespace Luce
```

### tendsto_zero_of_endpoint_power_bound

theorem; [source line 17](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailLimit.lean:17)

```lean
theorem tendsto_zero_of_endpoint_power_bound
    (f : ℝ → ℝ) (hf : ∀ α, 0 ≤ f α)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < δ →
      f (1 - ε) ≤ (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4)) :
    Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```


## Luce/Section4TailProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace Luce
```

### measurable_tailFixedPointCount

lemma; [source line 14](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailProbability.lean:14)

```lean
lemma measurable_tailFixedPointCount {n : ℕ} (α : ℝ) :
    Measurable (fun e : Fin n → ℝ => tailFixedPointCount e α)
```

### tailFixedPointCount_le

lemma; [source line 26](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailProbability.lean:26)

```lean
lemma tailFixedPointCount_le {n : ℕ} (e : Fin n → ℝ) (α : ℝ) :
    tailFixedPointCount e α ≤ n
```

### integrable_tailFixedPointCount

lemma; [source line 31](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailProbability.lean:31)

```lean
lemma integrable_tailFixedPointCount {n : ℕ} (w : Weights n) (α : ℝ) :
    Integrable (fun e => (tailFixedPointCount e α : ℝ)) (exponentialRace w)
```

### tailFixedPointCount_probability_le_expectation

lemma; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailProbability.lean:40)

```lean
lemma tailFixedPointCount_probability_le_expectation {n : ℕ} (w : Weights n) (α : ℝ) :
    (exponentialRace w).real {e | 0 < tailFixedPointCount e α} ≤
      ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace w
```

### tailFixedPointCount_probability_eq

lemma; [source line 48](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailProbability.lean:48)

```lean
lemma tailFixedPointCount_probability_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (w : Weights n) (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (E i) (expMeasure (w.rate i)) P)
    (hIndependent : iIndepFun E P) (α : ℝ) :
    P.real {ω | 0 < tailFixedPointCount (fun i => E i ω) α} =
      (exponentialRace w).real {e | 0 < tailFixedPointCount e α}
```


## Luce/Section4TailTightness.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailTightness.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
universe u
namespace Luce
```

### tail_probability_le_epsilonTailExpectation

lemma; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailTightness.lean:25)

Markov's inequality for the exact spatial tail, expressed using the
existing terminal expectation. The joint law is derived from the approved
clock hypotheses.

```lean
lemma tail_probability_le_epsilonTailExpectation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (w : WeightArray) (n : ℕ) (E : Fin (n + 1) → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (E i) (expMeasure ((w (n + 1)).rate i)) P)
    (hIndependent : iIndepFun E P) {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    P.real {ω | 0 < tailFixedPointCount (fun i => E i ω) (1 - ε)} ≤
      epsilonTailExpectation (fun n => w (n + 1)) ε n
```

### tail_fixed_point_tightness

theorem; [source line 40](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TailTightness.lean:40)

The approved general-space form of `eq:tail-tightness`.
The constants in `EndpointAssumption` remain uniform in row size and label.

```lean
theorem tail_fixed_point_tightness
    (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray)
    (hnorm : NormalizedWeights w) (hend : EndpointAssumption w)
    (E : (n : ℕ) → Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) :
    Tendsto
      (fun α : ℝ => limsup
        (fun n : ℕ => (P n).real
          {ω | 0 < tailFixedPointCount (fun i => E n i ω) α}) atTop)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```


## Luce/Section4TwoCandidate.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TwoCandidate.lean)

Namespace / shared context (consult source for section boundaries):

```lean
namespace Luce
variable {α : Type*} [DecidableEq α]
```

### two_candidate_bound_finset

theorem; [source line 25](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TwoCandidate.lean:25)

Among any finite set of natural-number indices, at most two equal the
number of survivors remaining after their candidate is excluded.

```lean
theorem two_candidate_bound_finset (survivors : Finset α) (candidate : ℕ → α)
    (indices : Finset ℕ) :
    (indices.filter fun m => (survivors.erase (candidate m)).card = m).card ≤ 2
```

### two_candidate_bound

theorem; [source line 43](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TwoCandidate.lean:43)

The two-candidate bound for indices `0, ..., M - 1`.

```lean
theorem two_candidate_bound (survivors : Finset α) (candidate : ℕ → α) (M : ℕ) :
    ((Finset.range M).filter fun m => (survivors.erase (candidate m)).card = m).card ≤
      2
```

### two_candidate_bound_Icc

theorem; [source line 50](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TwoCandidate.lean:50)

The paper's counting bound, with indices `1, ..., M` and required count `m - 1`.
The positive lower bound on the indices avoids truncation of natural subtraction.

```lean
theorem two_candidate_bound_Icc (survivors : Finset α) (candidate : ℕ → α) (M : ℕ) :
    ((Finset.Icc 1 M).filter fun m =>
      (survivors.erase (candidate m)).card = m - 1).card ≤ 2
```

### two_candidate_sum_bound

theorem; [source line 72](D:/princeton/Research/Lean/Lean_luce/Luce/Section4TwoCandidate.lean:72)

Equation `eq:two-candidate` as a sum of natural-number indicators.

```lean
theorem two_candidate_sum_bound (survivors : Finset α) (candidate : ℕ → α) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M,
      if (survivors.erase (candidate m)).card = m - 1 then (1 : ℕ) else 0) ≤ 2
```


## Luce/Section2UncappedPoisson.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2UncappedPoisson.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce
namespace BernoulliProcess
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
```

### integral_difference_le_bad_probability

lemma; [source line 21](D:/princeton/Research/Lean/Lean_luce/Luce/Section2UncappedPoisson.lean:21)

```lean
private lemma integral_difference_le_bad_probability
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Ω → ℝ} (hAint : Integrable A μ) (hBint : Integrable B μ)
    (hA : ∀ ω, 0 ≤ A ω ∧ A ω ≤ 1) (hB : ∀ ω, 0 ≤ B ω ∧ B ω ≤ 1)
    (bad : Set Ω) (hbad : MeasurableSet bad) (heq : ∀ ω, ω ∉ bad → A ω = B ω) :
    |(∫ ω, A ω ∂μ) - ∫ ω, B ω ∂μ| ≤ μ.real bad
```

### uncapped_laplace_tendsto_rows

theorem; [source line 49](D:/princeton/Research/Lean/Lean_luce/Luce/Section2UncappedPoisson.lean:49)

The finite-row predictable Poisson Laplace limit with no deterministic
cap or assumptions on the original observations after the row ends.

```lean
theorem uncapped_laplace_tendsto_rows (X : ∀ n, BernoulliProcess (P n))
    (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) {c lam : ℝ}
    (hc : 0 ≤ c) (hlam : 0 ≤ lam) (hg : ∀ n k, 0 ≤ g n k)
    (htotal : ConvergesInProbability P
      (fun n ω => ∑ k ∈ Finset.range (N n), (X n).probability k ω) c)
    (hmax : ConvergesInProbability P (fun n => (X n).rowMaximum (N n)) 0)
    (hcomp : ConvergesInProbability P
      (fun n => (X n).laplaceCompensator (g n) (N n)) lam) :
    Tendsto (fun n => ∫ ω, Real.exp (-(∑ k ∈ Finset.range (N n),
      g n k * (X n).observation k ω)) ∂P n) atTop (𝓝 (Real.exp (-lam)))
```


## Luce/Section2WeakMeasureProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/Luce/Section2WeakMeasureProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
namespace Luce
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
namespace WeakMeasureConvergesInProbability
variable {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
```

### WeakMeasureConvergesInProbability

def; [source line 24](D:/princeton/Research/Lean/Lean_luce/Luce/Section2WeakMeasureProbability.lean:24)

Convergence to a deterministic finite measure in probability, tested
against every open neighborhood for the weak topology.

```lean
def WeakMeasureConvergesInProbability (P : ∀ n, Measure (Ω n))
    (A : ∀ n, Ω n → FiniteMeasure X) (ν : FiniteMeasure X) : Prop :=
  ∀ U : Set (FiniteMeasure X), IsOpen U → ν ∈ U →
    Tendsto (fun n => (P n).real {ω | A n ω ∉ U}) atTop (𝓝 0)
```

### integral

theorem; [source line 36](D:/princeton/Research/Lean/Lean_luce/Luce/Section2WeakMeasureProbability.lean:36)

Every bounded continuous real integral coordinate inherits convergence
in probability from the actual weak-neighborhood criterion.

```lean
theorem integral (hA : WeakMeasureConvergesInProbability P A ν) (f : X →ᵇ ℝ) :
    ConvergesInProbability P (fun n ω => ∫ x, f x ∂(A n ω : Measure X))
      (∫ x, f x ∂(ν : Measure X))
```


## proposals/Section2Compensator.lean

[Source](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
open scoped BigOperators
universe u
namespace Luce.Section2CompensatorProposal
```

### spatialPoint

def; [source line 25](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:25)

The paper's spatial point `(k.val + 1) / n`, with zero-based `Fin` labels.

```lean
noncomputable def spatialPoint {n : ℕ} (k : Fin n) : ℝ :=
  ((k.val + 1 : ℕ) : ℝ) / (n : ℝ)
```

### fixedPointIndicator

def; [source line 29](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:29)

The paper's rank-based fixed-point indicator.

```lean
def fixedPointIndicator {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) : ℝ :=
  if σ.symm k = k then 1 else 0
```

### fixedPointMeasurePrefix

def; [source line 34](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:34)

Fixed-point atoms observed after `m` draws. The process is constant for
`m ≥ n`, since only positions in `Fin n` occur.

```lean
noncomputable def fixedPointMeasurePrefix {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) (ω : Ω) : Measure ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < m),
    ENNReal.ofReal (fixedPointIndicator (π ω) k) • Measure.dirac (spatialPoint k)
```

### compensatorMeasurePrefix

def; [source line 41](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:41)

Cumulative proposed compensator atoms after `m` draws, using the explicit
probabilities from the approved conditional-probability theorem.

```lean
noncomputable def compensatorMeasurePrefix {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) (ω : Ω) : Measure ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < m),
    ENNReal.ofReal (predictableChance w (π ω) k) • Measure.dirac (spatialPoint k)
```

### fixedPointMeasure

def; [source line 47](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:47)

The manuscript's terminal fixed-point measure `Ξ_n`.

```lean
noncomputable def fixedPointMeasure {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (ω : Ω) : Measure ℝ :=
  fixedPointMeasurePrefix π n ω
```

### compensatorMeasure

def; [source line 52](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:52)

The manuscript's terminal compensator measure `A_n`.

```lean
noncomputable def compensatorMeasure {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (ω : Ω) : Measure ℝ :=
  compensatorMeasurePrefix w π n ω
```

### drawFiltration

def; [source line 58](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:58)

A structure wrapper whose sigma algebra at `m` is definitionally the
approved `drawHistory π m`. No larger or completed history is substituted.

```lean
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
```

### testedFixedPoint

def; [source line 74](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:74)

Integration of a deterministic spatial test against the cumulative
fixed-point measure.

```lean
noncomputable def testedFixedPoint {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (g : ℝ → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∫ x, g x ∂fixedPointMeasurePrefix π m ω
```

### testedCompensator

def; [source line 80](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:80)

Integration of a deterministic spatial test against the cumulative
compensator. Integrability is to follow from the finite deterministic support.

```lean
noncomputable def testedCompensator {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (g : ℝ → ℝ)
    (m : ℕ) (ω : Ω) : ℝ :=
  ∫ x, g x ∂compensatorMeasurePrefix w π m ω
```

### centeredTestedProcess

def; [source line 86](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:86)

The cumulative tested fixed-point process centered by its compensator.

```lean
noncomputable def centeredTestedProcess {Ω : Type u} {n : ℕ}
    (w : Weights n) (π : Ω → Equiv.Perm (Fin n)) (g : ℝ → ℝ)
    (m : ℕ) (ω : Ω) : ℝ :=
  testedFixedPoint π g m ω - testedCompensator w π g m ω
```

### CompensatorStatement

def; [source line 95](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Compensator.lean:95)

Proposed exact finite random-measure and tested predictable-compensator
claim. Finiteness, support, measure-valued measurability, spatial and sample
integrability, predictability, and the martingale property are conclusions,
rather than additional model inputs.

```lean
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
```


## proposals/Section2ConditionalProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/proposals/Section2ConditionalProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
universe u
namespace Luce.Section2ConditionalProposal
```

### PredictableProbabilityStatement

def; [source line 24](D:/princeton/Research/Lean/Lean_luce/proposals/Section2ConditionalProbability.lean:24)

Approved exact conditional expectation formula under the defining Luce
product law. Permutations have the discrete sigma algebra; equality of
conditional expectations is almost everywhere.

```lean
def PredictableProbabilityStatement : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [hP : IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n)),
    @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π →
    (∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ) →
    ∀ k : Fin n,
      P[(fun ω => if (π ω).symm k = k then (1 : ℝ) else 0)
          | drawHistory π k.val] =ᵐ[P]
        (fun ω =>
          (if k ≤ (π ω).symm k then w.rate k else 0) /
            w.total (remaining (π ω) k))
```


## proposals/Section2Predictability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Predictability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
universe u
namespace Luce.Section2Proposal
```

### drawHistory

def; [source line 25](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Predictability.lean:25)

The sigma algebra generated by the first `m` draws.
The label space has the discrete sigma algebra `⊤`. A zero-based position
`j` is among the first `m` draws exactly when `j.val < m`.

```lean
def drawHistory {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) : MeasurableSpace Ω :=
  ⨆ j : Fin n, ⨆ (_ : j.val < m),
    MeasurableSpace.comap (fun ω => π ω j) ⊤
```

### PredictabilityStatement

def; [source line 34](D:/princeton/Research/Lean/Lean_luce/proposals/Section2Predictability.lean:34)

Approved type of the Section 2 measurability assertion.
The Lean position `k` represents the paper's position `k.val + 1`, so its
pre-draw history contains exactly `k.val` draws.

```lean
def PredictabilityStatement : Prop :=
  ∀ {Ω : Type u} {n : ℕ} (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n)) (k : Fin n),
    Measurable[drawHistory π k.val]
      (fun ω => if k ≤ (π ω).symm k then (1 : ℝ) else 0) ∧
    Measurable[drawHistory π k.val]
      (fun ω => w.total (remaining (π ω) k))
```


## proposals/Section4TailTightness.lean

[Source](D:/princeton/Research/Lean/Lean_luce/proposals/Section4TailTightness.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
universe u
namespace Luce.Section4Proposal
```

### tailFixedPointCount

def; [source line 30](D:/princeton/Research/Lean/Lean_luce/proposals/Section4TailTightness.lean:30)

Approved exact count of the fixed-point atoms in `(α, 1]`.
The paper's label is `k.val + 1`. Row zero has no labels, so its count is zero.
For a positive row size, `α * n < k.val + 1` is exactly `(k.val + 1) / n > α`.

```lean
noncomputable def tailFixedPointCount {n : ℕ}
    (e : Fin n → ℝ) (α : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun k : Fin n =>
    α * (n : ℝ) < (k.val : ℝ) + 1 ∧ rankOf e k = k.val + 1).card
```

### TailTightnessStatement

def; [source line 38](D:/princeton/Research/Lean/Lean_luce/proposals/Section4TailTightness.lean:38)

The approved full type of the theorem. This definition does not
provide a proof or an assumption that the proposition holds.

```lean
def TailTightnessStatement : Prop :=
  ∀ (Ω : ℕ → Type u) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [hP : ∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray),
    NormalizedWeights w → EndpointAssumption w →
    ∀ E : (n : ℕ) → Fin n → Ω n → ℝ,
      (∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n)) →
      (∀ n, iIndepFun (E n) (P n)) →
      Tendsto
        (fun α : ℝ => limsup
          (fun n : ℕ => (P n).real
            {ω | 0 < tailFixedPointCount (fun i => E n i ω) α}) atTop)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```


## audit/Sections1To7AllProvedStatements.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Sections1To7AllProvedStatements.lean)

No declarations; imports or audit commands only.


## audit/Section1Assumptions.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section1Assumptions.lean)

No declarations; imports or audit commands only.


## audit/Section4DiscreteTotalVariation.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section4DiscreteTotalVariation.lean)

No declarations; imports or audit commands only.


## audit/Section2HistoryPredictability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section2HistoryPredictability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
universe u
namespace Luce.Section2LockedAudit
```

### drawHistory

def; [source line 13](D:/princeton/Research/Lean/Lean_luce/audit/Section2HistoryPredictability.lean:13)

```lean
def drawHistory {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) : MeasurableSpace Ω :=
  ⨆ j : Fin n, ⨆ (_ : j.val < m),
    MeasurableSpace.comap (fun ω => π ω j) ⊤
```

### PredictabilityStatement

def; [source line 18](D:/princeton/Research/Lean/Lean_luce/audit/Section2HistoryPredictability.lean:18)

```lean
def PredictabilityStatement : Prop :=
  ∀ {Ω : Type u} {n : ℕ} (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n)) (k : Fin n),
    Measurable[drawHistory π k.val]
      (fun ω => if k ≤ (π ω).symm k then (1 : ℝ) else 0) ∧
    Measurable[drawHistory π k.val]
      (fun ω => w.total (remaining (π ω) k))
```

### approved_history

theorem; [source line 26](D:/princeton/Research/Lean/Lean_luce/audit/Section2HistoryPredictability.lean:26)

```lean
theorem approved_history {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) :
    drawHistory π m = Luce.drawHistory π m
```

### approved_statement

theorem; [source line 30](D:/princeton/Research/Lean/Lean_luce/audit/Section2HistoryPredictability.lean:30)

```lean
theorem approved_statement : PredictabilityStatement.{u}
```


## audit/Section5Lemma52.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5Lemma52.lean)

No declarations; imports or audit commands only.


## audit/Section5Lemma52Proof.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5Lemma52Proof.lean)

No declarations; imports or audit commands only.


## audit/Section5Lemma52StatementCheck.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5Lemma52StatementCheck.lean)

No declarations; imports or audit commands only.


## audit/Section2PoissonCriterion.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section2PoissonCriterion.lean)

No declarations; imports or audit commands only.


## audit/Section2PredictableProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section2PredictableProbability.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory
universe u
namespace Luce.Section2ConditionalLockedAudit
```

### PredictableProbabilityStatement

def; [source line 11](D:/princeton/Research/Lean/Lean_luce/audit/Section2PredictableProbability.lean:11)

```lean
def PredictableProbabilityStatement : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [hP : IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n)),
    @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π →
    (∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ) →
    ∀ k : Fin n,
      P[(fun ω => if (π ω).symm k = k then (1 : ℝ) else 0)
          | drawHistory π k.val] =ᵐ[P]
        (fun ω =>
          (if k ≤ (π ω).symm k then w.rate k else 0) /
            w.total (remaining (π ω) k))
```

### approved_statement

theorem; [source line 24](D:/princeton/Research/Lean/Lean_luce/audit/Section2PredictableProbability.lean:24)

```lean
theorem approved_statement : PredictableProbabilityStatement.{u}
```


## audit/Section5Proposition54.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5Proposition54.lean)

No declarations; imports or audit commands only.


## audit/Section5Proposition54Proof.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5Proposition54Proof.lean)

No declarations; imports or audit commands only.


## audit/Section4RankIntegral.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section4RankIntegral.lean)

No declarations; imports or audit commands only.


## audit/Section2Existing.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section2Existing.lean)

No declarations; imports or audit commands only.


## audit/Section3.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section3.lean)

No declarations; imports or audit commands only.


## audit/Section4.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section4.lean)

No declarations; imports or audit commands only.


## audit/Section4Existing.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section4Existing.lean)

No declarations; imports or audit commands only.


## audit/Section5.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5.lean)

No declarations; imports or audit commands only.


## audit/Section5BulkPointProbability.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5BulkPointProbability.lean)

No declarations; imports or audit commands only.


## audit/Section5ContractAndRoots.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5ContractAndRoots.lean)

No declarations; imports or audit commands only.


## audit/Section5CycleShell.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5CycleShell.lean)

No declarations; imports or audit commands only.


## audit/Section5EarlyLate.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5EarlyLate.lean)

No declarations; imports or audit commands only.


## audit/Section5FactorialLocal.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5FactorialLocal.lean)

No declarations; imports or audit commands only.


## audit/Section5FactorialMoments.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5FactorialMoments.lean)

No declarations; imports or audit commands only.


## audit/Section5FactorialSieve.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5FactorialSieve.lean)

No declarations; imports or audit commands only.


## audit/Section5Final.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5Final.lean)

No declarations; imports or audit commands only.


## audit/Section5IntensityFinite.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5IntensityFinite.lean)

No declarations; imports or audit commands only.


## audit/Section5LateDecomposition.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5LateDecomposition.lean)

No declarations; imports or audit commands only.


## audit/Section5MaximumCylinder.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5MaximumCylinder.lean)

No declarations; imports or audit commands only.


## audit/Section5RetainedTightness.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5RetainedTightness.lean)

No declarations; imports or audit commands only.


## audit/Section5ShellProgress.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section5ShellProgress.lean)

No declarations; imports or audit commands only.


## audit/Section4ShellMigrationStatements.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section4ShellMigrationStatements.lean)

No declarations; imports or audit commands only.


## audit/Section4TailTightness.lean

[Source](D:/princeton/Research/Lean/Lean_luce/audit/Section4TailTightness.lean)

Namespace / shared context (consult source for section boundaries):

```lean
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
universe u
namespace Luce.Section4LockedAudit
```

### tailFixedPointCount

def; [source line 15](D:/princeton/Research/Lean/Lean_luce/audit/Section4TailTightness.lean:15)

```lean
noncomputable def tailFixedPointCount {n : ℕ}
    (e : Fin n → ℝ) (α : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun k : Fin n =>
    α * (n : ℝ) < (k.val : ℝ) + 1 ∧ rankOf e k = k.val + 1).card
```

### TailTightnessStatement

def; [source line 21](D:/princeton/Research/Lean/Lean_luce/audit/Section4TailTightness.lean:21)

```lean
def TailTightnessStatement : Prop :=
  ∀ (Ω : ℕ → Type u) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [hP : ∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray),
    NormalizedWeights w → EndpointAssumption w →
    ∀ E : (n : ℕ) → Fin n → Ω n → ℝ,
      (∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n)) →
      (∀ n, iIndepFun (E n) (P n)) →
      Tendsto
        (fun α : ℝ => limsup
          (fun n : ℕ => (P n).real
            {ω | 0 < tailFixedPointCount (fun i => E n i ω) α}) atTop)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))
```

### approved_count

theorem; [source line 35](D:/princeton/Research/Lean/Lean_luce/audit/Section4TailTightness.lean:35)

```lean
theorem approved_count {n : ℕ} (e : Fin n → ℝ) (α : ℝ) :
    tailFixedPointCount e α = Luce.tailFixedPointCount e α
```

### approved_statement

theorem; [source line 38](D:/princeton/Research/Lean/Lean_luce/audit/Section4TailTightness.lean:38)

```lean
theorem approved_statement : TailTightnessStatement.{u}
```
