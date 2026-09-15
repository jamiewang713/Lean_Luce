# Lean module names by paper section

The file names follow the numbered sections of `fixed_points_sampled_profile.tex`.
Modules already carrying a section prefix keep their names. Shared helpers are
assigned to the section whose argument they support; the Sukhatme modules use
Section 1 for Corollary 1.9, whose sampling argument is in Section 6.7.

`Section65` means subsection 6.5; `Section66` on audit files means subsection 6.6.
`Sections1To7` identifies the whole-project entry point and whole-project audits.

File and import names changed; public mathematical namespaces and theorem names
are unchanged. For example, `Luce.Section1Sukhatme` is the module containing
`Luce.Sukhatme.corollary19`.

Historical logs, JSON inventories, and frozen hash baselines retain their original
paths and bytes. Use this table to locate the renamed sources; those snapshots
record earlier revisions and are not fresh verification of the renamed files.

## Renamed files

| Previous path | Current path |
|---|---|
| `Luce.lean` | [Luce/Sections1To7.lean](../Luce/Sections1To7.lean) |
| `Luce/ApprovedRankIntegral.lean` | [Luce/Section4ApprovedRankIntegral.lean](../Luce/Section4ApprovedRankIntegral.lean) |
| `Luce/Assumptions.lean` | [Luce/Section1Assumptions.lean](../Luce/Section1Assumptions.lean) |
| `Luce/Basic.lean` | [Luce/Section1Basic.lean](../Luce/Section1Basic.lean) |
| `Luce/BernoulliCLT.lean` | [Luce/Section6BernoulliCLT.lean](../Luce/Section6BernoulliCLT.lean) |
| `Luce/BernoulliCLTCapped.lean` | [Luce/Section6BernoulliCLTCapped.lean](../Luce/Section6BernoulliCLTCapped.lean) |
| `Luce/BernoulliCLTStopping.lean` | [Luce/Section6BernoulliCLTStopping.lean](../Luce/Section6BernoulliCLTStopping.lean) |
| `Luce/BernoulliCharacteristic.lean` | [Luce/Section6BernoulliCharacteristic.lean](../Luce/Section6BernoulliCharacteristic.lean) |
| `Luce/BernoulliCharacteristicDrift.lean` | [Luce/Section6BernoulliCharacteristicDrift.lean](../Luce/Section6BernoulliCharacteristicDrift.lean) |
| `Luce/BernoulliCharacteristicEstimates.lean` | [Luce/Section6BernoulliCharacteristicEstimates.lean](../Luce/Section6BernoulliCharacteristicEstimates.lean) |
| `Luce/BernoulliCountTightness.lean` | [Luce/Section2BernoulliCountTightness.lean](../Luce/Section2BernoulliCountTightness.lean) |
| `Luce/BernoulliGaussianScale.lean` | [Luce/Section6BernoulliGaussianScale.lean](../Luce/Section6BernoulliGaussianScale.lean) |
| `Luce/BernoulliPointMeasure.lean` | [Luce/Section2BernoulliPointMeasure.lean](../Luce/Section2BernoulliPointMeasure.lean) |
| `Luce/BernoulliProcess.lean` | [Luce/Section2BernoulliProcess.lean](../Luce/Section2BernoulliProcess.lean) |
| `Luce/BernoulliReferenceApproximation.lean` | [Luce/Section6BernoulliReferenceApproximation.lean](../Luce/Section6BernoulliReferenceApproximation.lean) |
| `Luce/BernoulliReferenceMean.lean` | [Luce/Section6BernoulliReferenceMean.lean](../Luce/Section6BernoulliReferenceMean.lean) |
| `Luce/CappedPoisson.lean` | [Luce/Section2CappedPoisson.lean](../Luce/Section2CappedPoisson.lean) |
| `Luce/CompactLaplaceApproximation.lean` | [Luce/Section2CompactLaplaceApproximation.lean](../Luce/Section2CompactLaplaceApproximation.lean) |
| `Luce/CompactLawConvergence.lean` | [Luce/Section2CompactLawConvergence.lean](../Luce/Section2CompactLawConvergence.lean) |
| `Luce/ComplexProbabilityConvergence.lean` | [Luce/Section6ComplexProbabilityConvergence.lean](../Luce/Section6ComplexProbabilityConvergence.lean) |
| `Luce/ConditionalProbabilityBasics.lean` | [Luce/Section2ConditionalProbabilityBasics.lean](../Luce/Section2ConditionalProbabilityBasics.lean) |
| `Luce/ConvergenceInProbability.lean` | [Luce/Section2ConvergenceInProbability.lean](../Luce/Section2ConvergenceInProbability.lean) |
| `Luce/CountableLawConvergence.lean` | [Luce/Section4CountableLawConvergence.lean](../Luce/Section4CountableLawConvergence.lean) |
| `Luce/CountableTotalVariation.lean` | [Luce/Section4CountableTotalVariation.lean](../Luce/Section4CountableTotalVariation.lean) |
| `Luce/DiscreteTotalVariation.lean` | [Luce/Section4DiscreteTotalVariation.lean](../Luce/Section4DiscreteTotalVariation.lean) |
| `Luce/DrawHistory.lean` | [Luce/Section2DrawHistory.lean](../Luce/Section2DrawHistory.lean) |
| `Luce/DrawHistoryPermutation.lean` | [Luce/Section2DrawHistoryPermutation.lean](../Luce/Section2DrawHistoryPermutation.lean) |
| `Luce/EmpiricalRace.lean` | [Luce/Section3EmpiricalRace.lean](../Luce/Section3EmpiricalRace.lean) |
| `Luce/Endpoint.lean` | [Luce/Section4EndpointEstimates.lean](../Luce/Section4EndpointEstimates.lean) |
| `Luce/EndpointAsymptotic.lean` | [Luce/Section4EndpointAsymptotic.lean](../Luce/Section4EndpointAsymptotic.lean) |
| `Luce/EndpointBlockCapacity.lean` | [Luce/Section4EndpointBlockCapacity.lean](../Luce/Section4EndpointBlockCapacity.lean) |
| `Luce/EndpointBlockExpectation.lean` | [Luce/Section4EndpointBlockExpectation.lean](../Luce/Section4EndpointBlockExpectation.lean) |
| `Luce/EndpointBlockIntegral.lean` | [Luce/Section4EndpointBlockIntegral.lean](../Luce/Section4EndpointBlockIntegral.lean) |
| `Luce/EndpointCapacityAnalytic.lean` | [Luce/Section4EndpointCapacityAnalytic.lean](../Luce/Section4EndpointCapacityAnalytic.lean) |
| `Luce/EndpointCapacityChernoff.lean` | [Luce/Section4EndpointCapacityChernoff.lean](../Luce/Section4EndpointCapacityChernoff.lean) |
| `Luce/EndpointCapacityProbability.lean` | [Luce/Section4EndpointCapacityProbability.lean](../Luce/Section4EndpointCapacityProbability.lean) |
| `Luce/EndpointCutoff.lean` | [Luce/Section4EndpointCutoff.lean](../Luce/Section4EndpointCutoff.lean) |
| `Luce/EndpointExceptional.lean` | [Luce/Section4EndpointExceptional.lean](../Luce/Section4EndpointExceptional.lean) |
| `Luce/EndpointExceptionalTheorem.lean` | [Luce/Section4EndpointExceptionalTheorem.lean](../Luce/Section4EndpointExceptionalTheorem.lean) |
| `Luce/EndpointExpectationTightness.lean` | [Luce/Section4EndpointExpectationTightness.lean](../Luce/Section4EndpointExpectationTightness.lean) |
| `Luce/EndpointIntegrals.lean` | [Luce/Section4EndpointIntegrals.lean](../Luce/Section4EndpointIntegrals.lean) |
| `Luce/EndpointJensen.lean` | [Luce/Section4EndpointJensen.lean](../Luce/Section4EndpointJensen.lean) |
| `Luce/EndpointProbability.lean` | [Luce/Section4EndpointProbability.lean](../Luce/Section4EndpointProbability.lean) |
| `Luce/EndpointRace.lean` | [Luce/Section4EndpointRace.lean](../Luce/Section4EndpointRace.lean) |
| `Luce/EndpointRegularShellLimit.lean` | [Luce/Section4EndpointRegularShellLimit.lean](../Luce/Section4EndpointRegularShellLimit.lean) |
| `Luce/EndpointRegularShells.lean` | [Luce/Section4EndpointRegularShells.lean](../Luce/Section4EndpointRegularShells.lean) |
| `Luce/EndpointShellBuffer.lean` | [Luce/Section4EndpointShellBuffer.lean](../Luce/Section4EndpointShellBuffer.lean) |
| `Luce/EndpointShellBufferLimit.lean` | [Luce/Section4EndpointShellBufferLimit.lean](../Luce/Section4EndpointShellBufferLimit.lean) |
| `Luce/EndpointShellCompatibility.lean` | [Luce/Section4EndpointShellCompatibility.lean](../Luce/Section4EndpointShellCompatibility.lean) |
| `Luce/EndpointShellCover.lean` | [Luce/Section4EndpointShellCover.lean](../Luce/Section4EndpointShellCover.lean) |
| `Luce/EndpointShellDefinitions.lean` | [Luce/Section4EndpointShellDefinitions.lean](../Luce/Section4EndpointShellDefinitions.lean) |
| `Luce/EndpointShellEarly.lean` | [Luce/Section4EndpointShellEarly.lean](../Luce/Section4EndpointShellEarly.lean) |
| `Luce/EndpointShellEstimate.lean` | [Luce/Section4EndpointShellEstimate.lean](../Luce/Section4EndpointShellEstimate.lean) |
| `Luce/EndpointShellExpectationLimit.lean` | [Luce/Section4EndpointShellExpectationLimit.lean](../Luce/Section4EndpointShellExpectationLimit.lean) |
| `Luce/EndpointShellGeometry.lean` | [Luce/Section4EndpointShellGeometry.lean](../Luce/Section4EndpointShellGeometry.lean) |
| `Luce/EndpointShellPartition.lean` | [Luce/Section4EndpointShellPartition.lean](../Luce/Section4EndpointShellPartition.lean) |
| `Luce/EndpointShellTailBridge.lean` | [Luce/Section4EndpointShellTailBridge.lean](../Luce/Section4EndpointShellTailBridge.lean) |
| `Luce/EndpointShellTightness.lean` | [Luce/Section4EndpointShellTightness.lean](../Luce/Section4EndpointShellTightness.lean) |
| `Luce/EndpointShells.lean` | [Luce/Section4EndpointShells.lean](../Luce/Section4EndpointShells.lean) |
| `Luce/EndpointSlowLabel.lean` | [Luce/Section4EndpointSlowLabel.lean](../Luce/Section4EndpointSlowLabel.lean) |
| `Luce/EndpointTailPoisson.lean` | [Luce/Section4EndpointTailPoisson.lean](../Luce/Section4EndpointTailPoisson.lean) |
| `Luce/EndpointTheorem.lean` | [Luce/Section4EndpointTheorem.lean](../Luce/Section4EndpointTheorem.lean) |
| `Luce/ExponentialFacts.lean` | [Luce/Section4ExponentialFacts.lean](../Luce/Section4ExponentialFacts.lean) |
| `Luce/ExponentialMemoryless.lean` | [Luce/Section3ExponentialMemoryless.lean](../Luce/Section3ExponentialMemoryless.lean) |
| `Luce/ExponentialRace.lean` | [Luce/Section4ExponentialRace.lean](../Luce/Section4ExponentialRace.lean) |
| `Luce/FiniteAdaptedBernoulli.lean` | [Luce/Section2FiniteAdaptedBernoulli.lean](../Luce/Section2FiniteAdaptedBernoulli.lean) |
| `Luce/FiniteBernoulliRow.lean` | [Luce/Section2FiniteBernoulliRow.lean](../Luce/Section2FiniteBernoulliRow.lean) |
| `Luce/FiniteBernoulliSpatial.lean` | [Luce/Section2FiniteBernoulliSpatial.lean](../Luce/Section2FiniteBernoulliSpatial.lean) |
| `Luce/FiniteHistoryConditional.lean` | [Luce/Section2FiniteHistoryConditional.lean](../Luce/Section2FiniteHistoryConditional.lean) |
| `Luce/FinitePointMeasure.lean` | [Luce/Section2FinitePointMeasure.lean](../Luce/Section2FinitePointMeasure.lean) |
| `Luce/FinitePoissonLaw.lean` | [Luce/Section2FinitePoissonLaw.lean](../Luce/Section2FinitePoissonLaw.lean) |
| `Luce/FirstChoice.lean` | [Luce/Section1FirstChoice.lean](../Luce/Section1FirstChoice.lean) |
| `Luce/HistoryAtoms.lean` | [Luce/Section2HistoryAtoms.lean](../Luce/Section2HistoryAtoms.lean) |
| `Luce/HistoryPredictability.lean` | [Luce/Section2HistoryPredictability.lean](../Luce/Section2HistoryPredictability.lean) |
| `Luce/Interior.lean` | [Luce/Section3Interior.lean](../Luce/Section3Interior.lean) |
| `Luce/LaplaceCountTightness.lean` | [Luce/Section4LaplaceCountTightness.lean](../Luce/Section4LaplaceCountTightness.lean) |
| `Luce/LikelihoodSecondMoment.lean` | [Luce/Section2LikelihoodSecondMoment.lean](../Luce/Section2LikelihoodSecondMoment.lean) |
| `Luce/LuceMassRecursion.lean` | [Luce/Section2LuceMassRecursion.lean](../Luce/Section2LuceMassRecursion.lean) |
| `Luce/LuceNextDraw.lean` | [Luce/Section2LuceNextDraw.lean](../Luce/Section2LuceNextDraw.lean) |
| `Luce/LucePrefixMass.lean` | [Luce/Section2LucePrefixMass.lean](../Luce/Section2LucePrefixMass.lean) |
| `Luce/LucePrefixRecursion.lean` | [Luce/Section2LucePrefixRecursion.lean](../Luce/Section2LucePrefixRecursion.lean) |
| `Luce/LucePrefixTransition.lean` | [Luce/Section2LucePrefixTransition.lean](../Luce/Section2LucePrefixTransition.lean) |
| `Luce/Model.lean` | [Luce/Section1Model.lean](../Luce/Section1Model.lean) |
| `Luce/PointMeasureLaplace.lean` | [Luce/Section2PointMeasureLaplace.lean](../Luce/Section2PointMeasureLaplace.lean) |
| `Luce/PointMeasureLawConvergence.lean` | [Luce/Section2PointMeasureLawConvergence.lean](../Luce/Section2PointMeasureLawConvergence.lean) |
| `Luce/PoissonCriterion.lean` | [Luce/Section2PoissonCriterion.lean](../Luce/Section2PoissonCriterion.lean) |
| `Luce/PoissonMixture.lean` | [Luce/Section2PoissonMixture.lean](../Luce/Section2PoissonMixture.lean) |
| `Luce/Predictable.lean` | [Luce/Section2Predictable.lean](../Luce/Section2Predictable.lean) |
| `Luce/PredictablePoisson.lean` | [Luce/Section2PredictablePoisson.lean](../Luce/Section2PredictablePoisson.lean) |
| `Luce/PredictableProbability.lean` | [Luce/Section2PredictableProbability.lean](../Luce/Section2PredictableProbability.lean) |
| `Luce/ProbabilityConvergence.lean` | [Luce/Section2ProbabilityConvergence.lean](../Luce/Section2ProbabilityConvergence.lean) |
| `Luce/Profile.lean` | [Luce/Section3ProfileKernels.lean](../Luce/Section3ProfileKernels.lean) |
| `Luce/ProfileRegularity.lean` | [Luce/Section3ProfileRegularity.lean](../Luce/Section3ProfileRegularity.lean) |
| `Luce/RaceConvergence.lean` | [Luce/Section3RaceConvergence.lean](../Luce/Section3RaceConvergence.lean) |
| `Luce/RaceOrder.lean` | [Luce/Section1RaceOrder.lean](../Luce/Section1RaceOrder.lean) |
| `Luce/RankIntegral.lean` | [Luce/Section4RankIntegral.lean](../Luce/Section4RankIntegral.lean) |
| `Luce/RankIntegralDependencyAudit.lean` | [Luce/Section4RankIntegralDependencyAudit.lean](../Luce/Section4RankIntegralDependencyAudit.lean) |
| `Luce/RankProbability.lean` | [Luce/Section4RankProbability.lean](../Luce/Section4RankProbability.lean) |
| `Luce/ShellContractCheck.lean` | [Luce/Section4ShellContractCheck.lean](../Luce/Section4ShellContractCheck.lean) |
| `Luce/ShellContractRepresentation.lean` | [Luce/Section4ShellContractRepresentation.lean](../Luce/Section4ShellContractRepresentation.lean) |
| `Luce/ShellMigrationContract.lean` | [Luce/Section4ShellMigrationContract.lean](../Luce/Section4ShellMigrationContract.lean) |
| `Luce/ShellMigrationFoundations.lean` | [Luce/Section4ShellMigrationFoundations.lean](../Luce/Section4ShellMigrationFoundations.lean) |
| `Luce/SpatialPoissonLaplace.lean` | [Luce/Section2SpatialPoissonLaplace.lean](../Luce/Section2SpatialPoissonLaplace.lean) |
| `Luce/Stopping.lean` | [Luce/Section2Stopping.lean](../Luce/Section2Stopping.lean) |
| `Luce/Sukhatme.lean` | [Luce/Section1Sukhatme.lean](../Luce/Section1Sukhatme.lean) |
| `Luce/SukhatmeConstants.lean` | [Luce/Section1SukhatmeConstants.lean](../Luce/Section1SukhatmeConstants.lean) |
| `Luce/SukhatmeContract.lean` | [Luce/Section1SukhatmeContract.lean](../Luce/Section1SukhatmeContract.lean) |
| `Luce/SukhatmeDefinitions.lean` | [Luce/Section1SukhatmeDefinitions.lean](../Luce/Section1SukhatmeDefinitions.lean) |
| `Luce/SukhatmeProfile.lean` | [Luce/Section1SukhatmeProfile.lean](../Luce/Section1SukhatmeProfile.lean) |
| `Luce/TailAssumptions.lean` | [Luce/Section4TailAssumptions.lean](../Luce/Section4TailAssumptions.lean) |
| `Luce/TailCount.lean` | [Luce/Section4TailCount.lean](../Luce/Section4TailCount.lean) |
| `Luce/TailCountIndex.lean` | [Luce/Section4TailCountIndex.lean](../Luce/Section4TailCountIndex.lean) |
| `Luce/TailLimit.lean` | [Luce/Section4TailLimit.lean](../Luce/Section4TailLimit.lean) |
| `Luce/TailProbability.lean` | [Luce/Section4TailProbability.lean](../Luce/Section4TailProbability.lean) |
| `Luce/TailTightness.lean` | [Luce/Section4TailTightness.lean](../Luce/Section4TailTightness.lean) |
| `Luce/TwoCandidate.lean` | [Luce/Section4TwoCandidate.lean](../Luce/Section4TwoCandidate.lean) |
| `Luce/UncappedPoisson.lean` | [Luce/Section2UncappedPoisson.lean](../Luce/Section2UncappedPoisson.lean) |
| `Luce/WeakMeasureProbability.lean` | [Luce/Section2WeakMeasureProbability.lean](../Luce/Section2WeakMeasureProbability.lean) |
| `audit/AllProvedStatements.lean` | [audit/Sections1To7AllProvedStatements.lean](../audit/Sections1To7AllProvedStatements.lean) |
| `audit/Assumptions.lean` | [audit/Section1Assumptions.lean](../audit/Section1Assumptions.lean) |
| `audit/CurrentInventory.lean` | [audit/Sections1To7CurrentInventory.lean](../audit/Sections1To7CurrentInventory.lean) |
| `audit/DiscreteTotalVariation.lean` | [audit/Section4DiscreteTotalVariation.lean](../audit/Section4DiscreteTotalVariation.lean) |
| `audit/HistoryPredictability.lean` | [audit/Section2HistoryPredictability.lean](../audit/Section2HistoryPredictability.lean) |
| `audit/IndependentReview.lean` | [audit/Sections1To7IndependentReview.lean](../audit/Sections1To7IndependentReview.lean) |
| `audit/IndependentReviewImports.lean` | [audit/Sections1To7IndependentReviewImports.lean](../audit/Sections1To7IndependentReviewImports.lean) |
| `audit/Lemma52.lean` | [audit/Section5Lemma52.lean](../audit/Section5Lemma52.lean) |
| `audit/Lemma52Proof.lean` | [audit/Section5Lemma52Proof.lean](../audit/Section5Lemma52Proof.lean) |
| `audit/Lemma52StatementCheck.lean` | [audit/Section5Lemma52StatementCheck.lean](../audit/Section5Lemma52StatementCheck.lean) |
| `audit/PoissonCriterion.lean` | [audit/Section2PoissonCriterion.lean](../audit/Section2PoissonCriterion.lean) |
| `audit/PredictableProbability.lean` | [audit/Section2PredictableProbability.lean](../audit/Section2PredictableProbability.lean) |
| `audit/Proposition54.lean` | [audit/Section5Proposition54.lean](../audit/Section5Proposition54.lean) |
| `audit/Proposition54Proof.lean` | [audit/Section5Proposition54Proof.lean](../audit/Section5Proposition54Proof.lean) |
| `audit/RankIntegral.lean` | [audit/Section4RankIntegral.lean](../audit/Section4RankIntegral.lean) |
| `audit/ShellMigrationStatements.lean` | [audit/Section4ShellMigrationStatements.lean](../audit/Section4ShellMigrationStatements.lean) |
| `audit/Sukhatme.lean` | [audit/Section1Sukhatme.lean](../audit/Section1Sukhatme.lean) |
| `audit/TailTightness.lean` | [audit/Section4TailTightness.lean](../audit/Section4TailTightness.lean) |
