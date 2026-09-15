# Proposition 6.5 order-transfer proof evidence

Status: Proposition65Contract.localLaw and proposition65_contractCheck remain UNPROVED.
These are supporting theorems, not a completed Proposition 6.5.

Full current source/type/axiom audit: 711 declarations; permitted axioms only.

## Actual elaborated theorem types and transitive axiom output

### deleted_order_normalized_integral

```lean
theorem Luce.Section6.deleted_order_normalized_integral : ∀ {n : Nat} (w : Luce.Weights n)
  (removed : Finset.{0} (Fin n))
  (sigma :
    Equiv.Perm.{1}
      (Fin
        (@Finset.card.{0} (Fin n)
          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))))
  (H :
    (Fin
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)) →
        Real) →
      Real),
  @Measurable.{0, 0}
      (Fin
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)) →
        Real)
      Real
      (@MeasurableSpace.pi.{0, 0}
        (Fin
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
        (fun a => Real) fun a => Real.measurableSpace)
      Real.measurableSpace H →
    @Eq.{1} Real
      (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
        (@MeasureTheory.Measure.restrict.{0} (Fin n → Real)
          (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace) (@Luce.exponentialRace n w)
          (@Set.ofPred.{0} (Fin n → Real) fun old =>
            @StrictMono.{0, 0}
              (Fin
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
              Real
              (@PartialOrder.toPreorder.{0}
                (Fin
                  (@Finset.card.{0} (Fin n)
                    (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                      (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                (@Fin.instPartialOrder
                  (@Finset.card.{0} (Fin n)
                    (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                      (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))))
              Real.instPreorder fun l =>
              @Luce.compactDeletedClocks n removed old
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.Perm.{1}
                    (Fin
                      (@Finset.card.{0} (Fin n)
                        (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                          (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))))
                  (Fin
                    (@Finset.card.{0} (Fin n)
                      (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                        (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                  (fun x =>
                    Fin
                      (@Finset.card.{0} (Fin n)
                        (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                          (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.Perm.{1}
                      (Fin
                        (@Finset.card.{0} (Fin n)
                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))))
                    (Fin
                      (@Finset.card.{0} (Fin n)
                        (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                          (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                    (Fin
                      (@Finset.card.{0} (Fin n)
                        (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                          (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                    (@Equiv.instEquivLike.{1, 1}
                      (Fin
                        (@Finset.card.{0} (Fin n)
                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                      (Fin
                        (@Finset.card.{0} (Fin n)
                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))))
                  sigma l)))
        fun old =>
        H
          (@Luce.orderedNormalizedGaps
            (@Finset.card.{0} (Fin n)
              (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
            (@Luce.compactDeletedWeights n w removed) sigma (@Luce.compactDeletedClocks n removed old)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Luce.Weights.mass
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
          (@Luce.compactDeletedWeights n w removed) sigma)
        (@MeasureTheory.integral.{0, 0}
          (Fin
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)) →
            Real)
          Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (@MeasurableSpace.pi.{0, 0}
            (Fin
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
            (fun a => Real) fun a => Real.measurableSpace)
          (Luce.standardGapLaw
            (@Finset.card.{0} (Fin n)
              (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
          fun xi => H xi)) :=
⋯
'Luce.Section6.deleted_order_normalized_integral' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_order_kernel_product_integral

```lean
theorem Luce.Section6.deleted_order_kernel_product_integral : ∀ {n s : Nat} (w : Luce.Weights n)
  (removed : Finset.{0} (Fin n)) (u : Fin s → Fin n)
  (sigma :
    Equiv.Perm.{1}
      (Fin
        (@Finset.card.{0} (Fin n)
          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))))
  (q :
    Fin s →
      Fin
        (@Finset.card.{0} (Fin n)
          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))),
  have order :=
    @Set.ofPred.{0} (Fin n → Real) fun old =>
      @StrictMono.{0, 0}
        (Fin
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
        Real
        (@PartialOrder.toPreorder.{0}
          (Fin
            (@Finset.card.{0} (Fin n)
              (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
          (@Fin.instPartialOrder
            (@Finset.card.{0} (Fin n)
              (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))))
        Real.instPreorder fun l =>
        @Luce.compactDeletedClocks n removed old
          (@DFunLike.coe.{1, 1, 1}
            (Equiv.Perm.{1}
              (Fin
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))))
            (Fin
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
            (fun x =>
              Fin
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
            (@EquivLike.toFunLike.{1, 1, 1}
              (Equiv.Perm.{1}
                (Fin
                  (@Finset.card.{0} (Fin n)
                    (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                      (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))))
              (Fin
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
              (Fin
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
              (@Equiv.instEquivLike.{1, 1}
                (Fin
                  (@Finset.card.{0} (Fin n)
                    (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                      (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                (Fin
                  (@Finset.card.{0} (Fin n)
                    (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                      (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))))
            sigma l);
  And
    (@MeasureTheory.IntegrableOn.{0, 0} (Fin n → Real) Real
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@SeminormedAddGroup.toContinuousENorm.{0} Real
        (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))))
      (fun old =>
        ∏ e,
          (@Luce.deletedGapKernel n w removed old (u e)
              (@Fin.val
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                (q e))).toReal)
      order (@Luce.exponentialRace n w))
    (@Eq.{1} Real
      (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
        (@MeasureTheory.Measure.restrict.{0} (Fin n → Real)
          (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace) (@Luce.exponentialRace n w)
          order)
        fun old =>
        ∏ e,
          (@Luce.deletedGapKernel n w removed old (u e)
              (@Fin.val
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                (q e))).toReal)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Luce.Weights.mass
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
          (@Luce.compactDeletedWeights n w removed) sigma)
        (@MeasureTheory.integral.{0, 0}
          (Fin
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)) →
            Real)
          Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (@MeasurableSpace.pi.{0, 0}
            (Fin
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
            (fun a => Real) fun a => Real.measurableSpace)
          (Luce.standardGapLaw
            (@Finset.card.{0} (Fin n)
              (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
          fun xi =>
          ∏ e,
            Luce.exponentialGapMass (@Luce.Weights.rate n w (u e))
              (@Luce.Section6.gapStartFromNormalized
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                (@Luce.compactDeletedWeights n w removed) sigma (q e) xi)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (xi (q e))
                (@Luce.orderedRemainingRate
                  (@Finset.card.{0} (Fin n)
                    (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                      (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                  (@Luce.compactDeletedWeights n w removed) sigma (q e)))))) :=
⋯
'Luce.Section6.deleted_order_kernel_product_integral' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_kernel_product_order_sum

```lean
theorem Luce.Section6.deleted_kernel_product_order_sum : ∀ {n s : Nat} (w : Luce.Weights n)
  (removed : Finset.{0} (Fin n)) (u : Fin s → Fin n)
  (q :
    Fin s →
      Fin
        (@Finset.card.{0} (Fin n)
          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))),
  @Eq.{1} Real
    (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace) (@Luce.exponentialRace n w)
      fun old =>
      ∏ e,
        (@Luce.deletedGapKernel n w removed old (u e)
            (@Fin.val
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
              (q e))).toReal)
    (∑ sigma,
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Luce.Weights.mass
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
          (@Luce.compactDeletedWeights n w removed) sigma)
        (@MeasureTheory.integral.{0, 0}
          (Fin
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)) →
            Real)
          Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (@MeasurableSpace.pi.{0, 0}
            (Fin
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
            (fun a => Real) fun a => Real.measurableSpace)
          (Luce.standardGapLaw
            (@Finset.card.{0} (Fin n)
              (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
          fun xi =>
          ∏ e,
            Luce.exponentialGapMass (@Luce.Weights.rate n w (u e))
              (@Luce.Section6.gapStartFromNormalized
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                (@Luce.compactDeletedWeights n w removed) sigma (q e) xi)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (xi (q e))
                (@Luce.orderedRemainingRate
                  (@Finset.card.{0} (Fin n)
                    (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                      (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                  (@Luce.compactDeletedWeights n w removed) sigma (q e))))) :=
⋯
'Luce.Section6.deleted_kernel_product_order_sum' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### endpoint_block_terminal_buffer

```lean
theorem Luce.Section6.endpoint_block_terminal_buffer : ∀ {n r : Nat} {delta : Real},
  @LE.le.{0} Real Real.instLE delta
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯))) →
    ∀ (side : Luce.Section6.Corner) (j : Fin n),
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Luce.Section6.cornerDistance side n j) →
        @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (@Luce.Section6.cornerDistance side n j))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta
              (@Nat.cast.{0} Real Real.instNatCast n)) →
          @LT.lt.{0} Nat instLTNat r
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n (@Fin.val n j)) :=
⋯
'Luce.Section6.endpoint_block_terminal_buffer' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### sorted_gap_nonfinal_of_terminal_buffer

```lean
theorem Luce.Section6.sorted_gap_nonfinal_of_terminal_buffer : ∀ {n s r : Nat},
  @LE.le.{0} Nat instLENat s r →
    ∀ (u j : Fin s → Fin n),
      @Function.Injective.{1, 1} (Fin s) (Fin n) u →
        @Function.Injective.{1, 1} (Fin s) (Fin n) j →
          (∀ (e : Fin s),
              @LT.lt.{0} Nat instLTNat r
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n (@Fin.val n (j e)))) →
            ∀ (e : Fin s),
              @LT.lt.{0} Nat instLTNat (@Luce.sortedMarkedGapIndex n s j e)
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n))
                    (@Finset.image.{0, 0} (Fin s) (Fin n) (instDecidableEqFin n)
                      (@Function.comp.{1, 1, 1} (Fin s) (Fin s) (Fin n) u
                        (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (fun x => Fin s)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (Fin s)
                            (@Equiv.instEquivLike.{1, 1} (Fin s) (Fin s)))
                          (@Tuple.sort.{0} s (Fin n) (@Fin.instLinearOrder n) j)))
                      (@Finset.univ.{0} (Fin s) (Fin.fintype s))))) :=
⋯
'Luce.Section6.sorted_gap_nonfinal_of_terminal_buffer' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### separated_cylinder_order_sum

```lean
theorem Luce.Section6.separated_cylinder_order_sum : ∀ {n s r : Nat} (w : Luce.Weights n)
  (hs : @LE.le.{0} Nat instLENat s r) (u j : Fin s → Fin n) (hu : @Function.Injective.{1, 1} (Fin s) (Fin n) u)
  (hj : @Function.Injective.{1, 1} (Fin s) (Fin n) j),
  (∀ (a b : Fin s),
      @Ne.{1} (Fin s) a b →
        @LT.lt.{0} Nat instLTNat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
          ((@Fin.val n (j a)).dist (@Fin.val n (j b)))) →
    ∀
      (hbuffer :
        ∀ (e : Fin s),
          @LT.lt.{0} Nat instLTNat r
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n (@Fin.val n (j e)))),
      let removed :=
        @Finset.image.{0, 0} (Fin s) (Fin n) (instDecidableEqFin n)
          (@Function.comp.{1, 1, 1} (Fin s) (Fin s) (Fin n) u
            (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (fun x => Fin s)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (Fin s)
                (@Equiv.instEquivLike.{1, 1} (Fin s) (Fin s)))
              (@Tuple.sort.{0} s (Fin n) (@Fin.instLinearOrder n) j)))
          (@Finset.univ.{0} (Fin s) (Fin.fintype s));
      have q := fun e =>
        @Fin.mk
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
          (@Luce.sortedMarkedGapIndex n s j e) ⋯;
      @Eq.{1} Real
        (@MeasureTheory.Measure.real.{0} (Fin n → Real)
          (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace) (@Luce.exponentialRace n w)
          (@Set.ofPred.{0} (Fin n → Real) fun clocks => @Luce.MarkedRankCylinder n s u j clocks))
        (∑ sigma,
          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Luce.Weights.mass
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
              (@Luce.compactDeletedWeights n w removed) sigma)
            (@MeasureTheory.integral.{0, 0}
              (Fin
                  (@Finset.card.{0} (Fin n)
                    (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                      (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)) →
                Real)
              Real Real.normedAddCommGroup
              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
              (@MeasurableSpace.pi.{0, 0}
                (Fin
                  (@Finset.card.{0} (Fin n)
                    (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                      (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                (fun a => Real) fun a => Real.measurableSpace)
              (Luce.standardGapLaw
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
              fun xi =>
              ∏ e,
                Luce.exponentialGapMass
                  (@Luce.Weights.rate n w
                    (u
                      (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (fun x => Fin s)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (Fin s)
                          (@Equiv.instEquivLike.{1, 1} (Fin s) (Fin s)))
                        (@Tuple.sort.{0} s (Fin n) (@Fin.instLinearOrder n) j) e)))
                  (@Luce.Section6.gapStartFromNormalized
                    (@Finset.card.{0} (Fin n)
                      (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                        (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                    (@Luce.compactDeletedWeights n w removed) sigma (q e) xi)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (xi (q e))
                    (@Luce.orderedRemainingRate
                      (@Finset.card.{0} (Fin n)
                        (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                          (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                      (@Luce.compactDeletedWeights n w removed) sigma (q e))))) :=
⋯
'Luce.Section6.separated_cylinder_order_sum' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### normalized_insertion_product_bounds

```lean
theorem Luce.Section6.normalized_insertion_product_bounds.{u_1} : ∀ {n : Nat} {ι : Type u_1} [inst : Fintype.{u_1} ι]
  (w : Luce.Weights n) (sigma : Equiv.Perm.{1} (Fin n)) (q : ι → Fin n) (theta : ι → Real),
  (∀ (e : ι),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (theta e)) →
    ∀ (xi : Fin n → Real),
      (∀ (l : Fin n),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (xi l)) →
        And
          (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (∏ e,
              Luce.exponentialGapMass (theta e) (@Luce.Section6.gapStartFromNormalized n w sigma (q e) xi)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (xi (q e))
                  (@Luce.orderedRemainingRate n w sigma (q e)))))
          (@LE.le.{0} Real Real.instLE
            (∏ e,
              Luce.exponentialGapMass (theta e) (@Luce.Section6.gapStartFromNormalized n w sigma (q e) xi)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (xi (q e))
                  (@Luce.orderedRemainingRate n w sigma (q e))))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) :=
⋯
'Luce.Section6.normalized_insertion_product_bounds' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### normalized_insertion_product_integrable

```lean
theorem Luce.Section6.normalized_insertion_product_integrable.{u_1} : ∀ {n : Nat} {ι : Type u_1}
  [inst : Fintype.{u_1} ι] (w : Luce.Weights n) (sigma : Equiv.Perm.{1} (Fin n)) (q : ι → Fin n) (theta : ι → Real),
  (∀ (e : ι),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (theta e)) →
    @MeasureTheory.Integrable.{0, 0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@SeminormedAddGroup.toContinuousENorm.{0} Real
        (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))))
      (Fin n → Real) (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
      (fun xi =>
        ∏ e,
          Luce.exponentialGapMass (theta e) (@Luce.Section6.gapStartFromNormalized n w sigma (q e) xi)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (xi (q e))
              (@Luce.orderedRemainingRate n w sigma (q e))))
      (Luce.standardGapLaw n) :=
⋯
'Luce.Section6.normalized_insertion_product_integrable' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### normalized_skeleton_integral

```lean
theorem Luce.Section6.normalized_skeleton_integral : ∀ {n : Nat} (w : Luce.Weights n) (sigma : Equiv.Perm.{1} (Fin n))
  (S : Finset.{0} (Fin n)) (theta : Fin n → Real),
  (∀ (e : Fin n),
      @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) S e →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (theta e)) →
    have split :=
      @MeasurableEquiv.piEquivPiSubtypeProd.{0, 0} (Fin n) (fun x => Real) (fun x => Real.measurableSpace)
        (fun e =>
          @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) S e)
        fun a => @Finset.decidableMem.{0} (Fin n) (instDecidableEqFin n) a S;
    @Eq.{1} Real
      (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace) (Luce.standardGapLaw n)
        fun xi =>
        ∏ e,
          Luce.exponentialGapMass
            (theta
              (@Subtype.val.{1} (Fin n)
                (fun x =>
                  @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) S x)
                e))
            (@Luce.Section6.gapStartFromNormalized n w sigma
              (@Subtype.val.{1} (Fin n)
                (fun x =>
                  @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) S x)
                e)
              xi)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (xi
                (@Subtype.val.{1} (Fin n)
                  (fun x =>
                    @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) S
                      x)
                  e))
              (@Luce.orderedRemainingRate n w sigma
                (@Subtype.val.{1} (Fin n)
                  (fun x =>
                    @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) S
                      x)
                  e))))
      (@MeasureTheory.integral.{0, 0} ((@Subtype.{1} (Fin n) fun e => e ∉ S) → Real) Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin n) fun e => e ∉ S) (fun x => Real) fun i => Real.measurableSpace)
        (@MeasureTheory.Measure.pi.{0, 0} (@Subtype.{1} (Fin n) fun e => e ∉ S) (fun x => Real)
          (@Subtype.fintype.{0} (Fin n) (fun e => e ∉ S)
            (fun a =>
              @instDecidableNot
                (@Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) S a)
                (@Finset.decidableMem.{0} (Fin n) (instDecidableEqFin n) a S))
            (Fin.fintype n))
          (fun i => Real.measurableSpace) fun x =>
          ProbabilityTheory.expMeasure (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        fun z =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (∏ e,
            Real.exp
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Neg.neg.{0} Real Real.instNeg
                  (theta
                    (@Subtype.val.{1} (Fin n)
                      (fun x =>
                        @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                            (@Finset.instSetLike.{0} (Fin n)))
                          S x)
                      e)))
                (@Luce.Section6.skeletonStart n w sigma S
                  (@Subtype.val.{1} (Fin n)
                    (fun x =>
                      @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n)))
                        S x)
                    e)
                  (@DFunLike.coe.{1, 1, 1}
                    (@MeasurableEquiv.{0, 0} (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real))
                      (Fin n → Real)
                      (@Prod.instMeasurableSpace.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)
                        (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                        (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin n) fun i => i ∉ S) (fun i => Real) fun a =>
                          Real.measurableSpace))
                      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun x => Real.measurableSpace))
                    (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)) (fun x => Fin n → Real)
                    (@EquivLike.toFunLike.{1, 1, 1}
                      (@MeasurableEquiv.{0, 0} (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real))
                        (Fin n → Real)
                        (@Prod.instMeasurableSpace.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)
                          (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                          (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin n) fun i => i ∉ S) (fun i => Real) fun a =>
                            Real.measurableSpace))
                        (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun x => Real.measurableSpace))
                      (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)) (Fin n → Real)
                      (@MeasurableEquiv.instEquivLike.{0, 0}
                        (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)) (Fin n → Real)
                        (@Prod.instMeasurableSpace.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)
                          (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                          (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin n) fun i => i ∉ S) (fun i => Real) fun a =>
                            Real.measurableSpace))
                        (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun x => Real.measurableSpace)))
                    (@MeasurableEquiv.symm.{0, 0} (Fin n → Real)
                      (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real))
                      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun x => Real.measurableSpace)
                      (@Prod.instMeasurableSpace.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)
                        (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                        (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin n) fun i => i ∉ S) (fun i => Real) fun a =>
                          Real.measurableSpace))
                      split)
                    (@Prod.mk.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)
                      (@OfNat.ofNat.{0} (↥S → Real) (nat_lit 0)
                        (@Zero.toOfNat0.{0} (↥S → Real)
                          (@Pi.instZero.{0, 0} (↥S) (fun i => Real) fun i => Real.instZero)))
                      z)))))
          (∏ g,
            @HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Luce.orderedRemainingRate n w sigma
                  (@Subtype.val.{1} (Fin n)
                    (fun x =>
                      @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n)))
                        S x)
                    g))
                (theta
                  (@Subtype.val.{1} (Fin n)
                    (fun x =>
                      @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n)))
                        S x)
                    g)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Luce.orderedRemainingRate n w sigma
                    (@Subtype.val.{1} (Fin n)
                      (fun x =>
                        @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                            (@Finset.instSetLike.{0} (Fin n)))
                          S x)
                      g))
                  (@Luce.Section6.laterSelectedRate n S theta
                    (@Subtype.val.{1} (Fin n)
                      (fun x =>
                        @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                            (@Finset.instSetLike.{0} (Fin n)))
                          S x)
                      g)))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Luce.orderedRemainingRate n w sigma
                      (@Subtype.val.{1} (Fin n)
                        (fun x =>
                          @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                              (@Finset.instSetLike.{0} (Fin n)))
                            S x)
                        g))
                    (@Luce.Section6.laterSelectedRate n S theta
                      (@Subtype.val.{1} (Fin n)
                        (fun x =>
                          @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                              (@Finset.instSetLike.{0} (Fin n)))
                            S x)
                        g)))
                  (theta
                    (@Subtype.val.{1} (Fin n)
                      (fun x =>
                        @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                            (@Finset.instSetLike.{0} (Fin n)))
                          S x)
                      g)))))) :=
⋯
'Luce.Section6.normalized_skeleton_integral' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### later_selected_rate_reindex

```lean
theorem Luce.Section6.later_selected_rate_reindex : ∀ {n s : Nat} (q : Fin s → Fin n),
  @Function.Injective.{1, 1} (Fin s) (Fin n) q →
    ∀ (theta : Fin s → Real) (g : Fin n),
      @Eq.{1} Real
        (@Luce.Section6.laterSelectedRate n
          (@Finset.image.{0, 0} (Fin s) (Fin n) (instDecidableEqFin n) q (@Finset.univ.{0} (Fin s) (Fin.fintype s)))
          (@Function.extend.{1, 1, 1} (Fin s) (Fin n) Real q theta fun x =>
            @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          g)
        (∑ e with @LT.lt.{0} (Fin n) (@instLTFin n) g (q e), theta e) :=
⋯
'Luce.Section6.later_selected_rate_reindex' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### marked_normalized_skeleton_integral

```lean
theorem Luce.Section6.marked_normalized_skeleton_integral : ∀ {n s : Nat} (w : Luce.Weights n)
  (sigma : Equiv.Perm.{1} (Fin n)) (q : Fin s → Fin n),
  @Function.Injective.{1, 1} (Fin s) (Fin n) q →
    ∀ (theta : Fin s → Real),
      (∀ (e : Fin s),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (theta e)) →
        have S :=
          @Finset.image.{0, 0} (Fin s) (Fin n) (instDecidableEqFin n) q (@Finset.univ.{0} (Fin s) (Fin.fintype s));
        have thetaGap :=
          @Function.extend.{1, 1, 1} (Fin s) (Fin n) Real q theta fun x =>
            @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero);
        have split :=
          @MeasurableEquiv.piEquivPiSubtypeProd.{0, 0} (Fin n) (fun x => Real) (fun x => Real.measurableSpace)
            (fun e =>
              @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) S e)
            fun a => @Finset.decidableMem.{0} (Fin n) (instDecidableEqFin n) a S;
        @Eq.{1} Real
          (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace) (Luce.standardGapLaw n)
            fun xi =>
            ∏ e,
              Luce.exponentialGapMass (theta e) (@Luce.Section6.gapStartFromNormalized n w sigma (q e) xi)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (xi (q e))
                  (@Luce.orderedRemainingRate n w sigma (q e))))
          (@MeasureTheory.integral.{0, 0} ((@Subtype.{1} (Fin n) fun e => e ∉ S) → Real) Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin n) fun e => e ∉ S) (fun x => Real) fun i =>
              Real.measurableSpace)
            (@MeasureTheory.Measure.pi.{0, 0} (@Subtype.{1} (Fin n) fun e => e ∉ S) (fun x => Real)
              (@Subtype.fintype.{0} (Fin n) (fun e => e ∉ S)
                (fun a =>
                  @instDecidableNot
                    (@Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) S
                      a)
                    (@Finset.decidableMem.{0} (Fin n) (instDecidableEqFin n) a S))
                (Fin.fintype n))
              (fun i => Real.measurableSpace) fun x =>
              ProbabilityTheory.expMeasure (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            fun z =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (∏ e,
                Real.exp
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Neg.neg.{0} Real Real.instNeg
                      (thetaGap
                        (@Subtype.val.{1} (Fin n)
                          (fun x =>
                            @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                                (@Finset.instSetLike.{0} (Fin n)))
                              S x)
                          e)))
                    (@Luce.Section6.skeletonStart n w sigma S
                      (@Subtype.val.{1} (Fin n)
                        (fun x =>
                          @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                              (@Finset.instSetLike.{0} (Fin n)))
                            S x)
                        e)
                      (@DFunLike.coe.{1, 1, 1}
                        (@MeasurableEquiv.{0, 0}
                          (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)) (Fin n → Real)
                          (@Prod.instMeasurableSpace.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)
                            (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                            (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin n) fun i => i ∉ S) (fun i => Real) fun a =>
                              Real.measurableSpace))
                          (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun x => Real.measurableSpace))
                        (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)) (fun x => Fin n → Real)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (@MeasurableEquiv.{0, 0}
                            (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)) (Fin n → Real)
                            (@Prod.instMeasurableSpace.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)
                              (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                              (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin n) fun i => i ∉ S) (fun i => Real) fun a =>
                                Real.measurableSpace))
                            (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun x => Real.measurableSpace))
                          (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)) (Fin n → Real)
                          (@MeasurableEquiv.instEquivLike.{0, 0}
                            (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)) (Fin n → Real)
                            (@Prod.instMeasurableSpace.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)
                              (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                              (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin n) fun i => i ∉ S) (fun i => Real) fun a =>
                                Real.measurableSpace))
                            (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun x => Real.measurableSpace)))
                        (@MeasurableEquiv.symm.{0, 0} (Fin n → Real)
                          (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real))
                          (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun x => Real.measurableSpace)
                          (@Prod.instMeasurableSpace.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)
                            (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                            (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin n) fun i => i ∉ S) (fun i => Real) fun a =>
                              Real.measurableSpace))
                          split)
                        (@Prod.mk.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin n) fun i => i ∉ S) → Real)
                          (@OfNat.ofNat.{0} (↥S → Real) (nat_lit 0)
                            (@Zero.toOfNat0.{0} (↥S → Real)
                              (@Pi.instZero.{0, 0} (↥S) (fun i => Real) fun i => Real.instZero)))
                          z)))))
              (∏ g,
                @HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Luce.orderedRemainingRate n w sigma
                      (@Subtype.val.{1} (Fin n)
                        (fun x =>
                          @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                              (@Finset.instSetLike.{0} (Fin n)))
                            S x)
                        g))
                    (thetaGap
                      (@Subtype.val.{1} (Fin n)
                        (fun x =>
                          @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                              (@Finset.instSetLike.{0} (Fin n)))
                            S x)
                        g)))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@Luce.orderedRemainingRate n w sigma
                        (@Subtype.val.{1} (Fin n)
                          (fun x =>
                            @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                                (@Finset.instSetLike.{0} (Fin n)))
                              S x)
                          g))
                      (@Luce.Section6.laterSelectedRate n S thetaGap
                        (@Subtype.val.{1} (Fin n)
                          (fun x =>
                            @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                                (@Finset.instSetLike.{0} (Fin n)))
                              S x)
                          g)))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@Luce.orderedRemainingRate n w sigma
                          (@Subtype.val.{1} (Fin n)
                            (fun x =>
                              @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                                  (@Finset.instSetLike.{0} (Fin n)))
                                S x)
                            g))
                        (@Luce.Section6.laterSelectedRate n S thetaGap
                          (@Subtype.val.{1} (Fin n)
                            (fun x =>
                              @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                                  (@Finset.instSetLike.{0} (Fin n)))
                                S x)
                            g)))
                      (thetaGap
                        (@Subtype.val.{1} (Fin n)
                          (fun x =>
                            @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n)
                                (@Finset.instSetLike.{0} (Fin n)))
                              S x)
                          g)))))) :=
⋯
'Luce.Section6.marked_normalized_skeleton_integral' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### separated_cylinder_skeleton_formula

```lean
theorem Luce.Section6.separated_cylinder_skeleton_formula : ∀ {n s r : Nat} (w : Luce.Weights n)
  (hs : @LE.le.{0} Nat instLENat s r) (u j : Fin s → Fin n) (hu : @Function.Injective.{1, 1} (Fin s) (Fin n) u)
  (hj : @Function.Injective.{1, 1} (Fin s) (Fin n) j),
  (∀ (a b : Fin s),
      @Ne.{1} (Fin s) a b →
        @LT.lt.{0} Nat instLTNat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
          ((@Fin.val n (j a)).dist (@Fin.val n (j b)))) →
    ∀
      (hbuffer :
        ∀ (e : Fin s),
          @LT.lt.{0} Nat instLTNat r
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n (@Fin.val n (j e)))),
      let removed :=
        @Finset.image.{0, 0} (Fin s) (Fin n) (instDecidableEqFin n)
          (@Function.comp.{1, 1, 1} (Fin s) (Fin s) (Fin n) u
            (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (fun x => Fin s)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (Fin s)
                (@Equiv.instEquivLike.{1, 1} (Fin s) (Fin s)))
              (@Tuple.sort.{0} s (Fin n) (@Fin.instLinearOrder n) j)))
          (@Finset.univ.{0} (Fin s) (Fin.fintype s));
      let N :=
        @Finset.card.{0} (Fin n)
          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed);
      have q := fun e => @Fin.mk N (@Luce.sortedMarkedGapIndex n s j e) ⋯;
      have S :=
        @Finset.image.{0, 0} (Fin s) (Fin N) (instDecidableEqFin N) q (@Finset.univ.{0} (Fin s) (Fin.fintype s));
      have thetaGap :=
        @Function.extend.{1, 1, 1} (Fin s) (Fin N) Real q
          (fun e =>
            @Luce.Weights.rate n w
              (u
                (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (fun x => Fin s)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (Fin s)
                    (@Equiv.instEquivLike.{1, 1} (Fin s) (Fin s)))
                  (@Tuple.sort.{0} s (Fin n) (@Fin.instLinearOrder n) j) e)))
          fun x => @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero);
      have cw := @Luce.compactDeletedWeights n w removed;
      have split :=
        @MeasurableEquiv.piEquivPiSubtypeProd.{0, 0} (Fin N) (fun x => Real) (fun x => Real.measurableSpace)
          (fun e =>
            @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N) (@Finset.instSetLike.{0} (Fin N))) S e)
          fun a => @Finset.decidableMem.{0} (Fin N) (instDecidableEqFin N) a S;
      @Eq.{1} Real
        (@MeasureTheory.Measure.real.{0} (Fin n → Real)
          (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace) (@Luce.exponentialRace n w)
          (@Set.ofPred.{0} (Fin n → Real) fun clocks => @Luce.MarkedRankCylinder n s u j clocks))
        (∑ sigma,
          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Luce.Weights.mass
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
              cw sigma)
            (@MeasureTheory.integral.{0, 0} ((@Subtype.{1} (Fin N) fun e => e ∉ S) → Real) Real Real.normedAddCommGroup
              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
              (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin N) fun e => e ∉ S) (fun x => Real) fun i =>
                Real.measurableSpace)
              (@MeasureTheory.Measure.pi.{0, 0} (@Subtype.{1} (Fin N) fun e => e ∉ S) (fun x => Real)
                (@Subtype.fintype.{0} (Fin N) (fun e => e ∉ S)
                  (fun a =>
                    @instDecidableNot
                      (@Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N) (@Finset.instSetLike.{0} (Fin N)))
                        S a)
                      (@Finset.decidableMem.{0} (Fin N) (instDecidableEqFin N) a S))
                  (Fin.fintype N))
                (fun i => Real.measurableSpace) fun x =>
                ProbabilityTheory.expMeasure (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              fun z =>
              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (∏ e,
                  Real.exp
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (thetaGap
                          (@Subtype.val.{1} (Fin N)
                            (fun x =>
                              @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N)
                                  (@Finset.instSetLike.{0} (Fin N)))
                                S x)
                            e)))
                      (@Luce.Section6.skeletonStart
                        (@Finset.card.{0} (Fin n)
                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                        cw sigma S
                        (@Subtype.val.{1} (Fin N)
                          (fun x =>
                            @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N)
                                (@Finset.instSetLike.{0} (Fin N)))
                              S x)
                          e)
                        (@DFunLike.coe.{1, 1, 1}
                          (@MeasurableEquiv.{0, 0}
                            (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real)) (Fin N → Real)
                            (@Prod.instMeasurableSpace.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real)
                              (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                              (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin N) fun i => i ∉ S) (fun i => Real) fun a =>
                                Real.measurableSpace))
                            (@MeasurableSpace.pi.{0, 0} (Fin N) (fun x => Real) fun x => Real.measurableSpace))
                          (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real))
                          (fun x => Fin N → Real)
                          (@EquivLike.toFunLike.{1, 1, 1}
                            (@MeasurableEquiv.{0, 0}
                              (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real)) (Fin N → Real)
                              (@Prod.instMeasurableSpace.{0, 0} (↥S → Real)
                                ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real)
                                (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                                (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin N) fun i => i ∉ S) (fun i => Real)
                                  fun a => Real.measurableSpace))
                              (@MeasurableSpace.pi.{0, 0} (Fin N) (fun x => Real) fun x => Real.measurableSpace))
                            (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real)) (Fin N → Real)
                            (@MeasurableEquiv.instEquivLike.{0, 0}
                              (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real)) (Fin N → Real)
                              (@Prod.instMeasurableSpace.{0, 0} (↥S → Real)
                                ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real)
                                (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                                (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin N) fun i => i ∉ S) (fun i => Real)
                                  fun a => Real.measurableSpace))
                              (@MeasurableSpace.pi.{0, 0} (Fin N) (fun x => Real) fun x => Real.measurableSpace)))
                          (@MeasurableEquiv.symm.{0, 0} (Fin N → Real)
                            (Prod.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real))
                            (@MeasurableSpace.pi.{0, 0} (Fin N) (fun x => Real) fun x => Real.measurableSpace)
                            (@Prod.instMeasurableSpace.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real)
                              (@MeasurableSpace.pi.{0, 0} (↥S) (fun i => Real) fun a => Real.measurableSpace)
                              (@MeasurableSpace.pi.{0, 0} (@Subtype.{1} (Fin N) fun i => i ∉ S) (fun i => Real) fun a =>
                                Real.measurableSpace))
                            split)
                          (@Prod.mk.{0, 0} (↥S → Real) ((@Subtype.{1} (Fin N) fun i => i ∉ S) → Real)
                            (@OfNat.ofNat.{0} (↥S → Real) (nat_lit 0)
                              (@Zero.toOfNat0.{0} (↥S → Real)
                                (@Pi.instZero.{0, 0} (↥S) (fun i => Real) fun i => Real.instZero)))
                            z)))))
                (∏ g,
                  @HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Luce.orderedRemainingRate
                        (@Finset.card.{0} (Fin n)
                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                        cw sigma
                        (@Subtype.val.{1} (Fin N)
                          (fun x =>
                            @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N)
                                (@Finset.instSetLike.{0} (Fin N)))
                              S x)
                          g))
                      (thetaGap
                        (@Subtype.val.{1} (Fin N)
                          (fun x =>
                            @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N)
                                (@Finset.instSetLike.{0} (Fin N)))
                              S x)
                          g)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@Luce.orderedRemainingRate
                          (@Finset.card.{0} (Fin n)
                            (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                              (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                          cw sigma
                          (@Subtype.val.{1} (Fin N)
                            (fun x =>
                              @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N)
                                  (@Finset.instSetLike.{0} (Fin N)))
                                S x)
                            g))
                        (@Luce.Section6.laterSelectedRate N S thetaGap
                          (@Subtype.val.{1} (Fin N)
                            (fun x =>
                              @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N)
                                  (@Finset.instSetLike.{0} (Fin N)))
                                S x)
                            g)))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Luce.orderedRemainingRate
                            (@Finset.card.{0} (Fin n)
                              (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                                (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                                (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                            cw sigma
                            (@Subtype.val.{1} (Fin N)
                              (fun x =>
                                @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N)
                                    (@Finset.instSetLike.{0} (Fin N)))
                                  S x)
                              g))
                          (@Luce.Section6.laterSelectedRate N S thetaGap
                            (@Subtype.val.{1} (Fin N)
                              (fun x =>
                                @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N)
                                    (@Finset.instSetLike.{0} (Fin N)))
                                  S x)
                              g)))
                        (thetaGap
                          (@Subtype.val.{1} (Fin N)
                            (fun x =>
                              @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin N)) (Fin N)
                                  (@Finset.instSetLike.{0} (Fin N)))
                                S x)
                            g))))))) :=
⋯
'Luce.Section6.separated_cylinder_skeleton_formula' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### ordered_remaining_rate_antitone

```lean
theorem Luce.Section6.ordered_remaining_rate_antitone : ∀ {n : Nat} (w : Luce.Weights n)
  (sigma : Equiv.Perm.{1} (Fin n)),
  @Antitone.{0, 0} (Fin n) Real (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) Real.instPreorder
    (@Luce.orderedRemainingRate n w sigma) :=
⋯
'Luce.Section6.ordered_remaining_rate_antitone' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### skeleton_displacement_bound

```lean
theorem Luce.Section6.skeleton_displacement_bound : ∀ {n : Nat} (w : Luce.Weights n) (sigma : Equiv.Perm.{1} (Fin n))
  (S : Finset.{0} (Fin n)) (q : Fin n) (xi : Fin n → Real),
  (∀ (g : Fin n),
      @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) S g →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (xi g)) →
    And
      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@Luce.Section6.gapStartFromNormalized n w sigma q xi) (@Luce.Section6.skeletonStart n w sigma S q xi)))
      (@LE.le.{0} Real Real.instLE
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@Luce.Section6.gapStartFromNormalized n w sigma q xi) (@Luce.Section6.skeletonStart n w sigma S q xi))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (∑ g ∈ S, xi g) (@Luce.orderedRemainingRate n w sigma q))) :=
⋯
'Luce.Section6.skeleton_displacement_bound' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### bernoulli_sum_exp_integrable

```lean
theorem Luce.Section6.bernoulli_sum_exp_integrable.{u_1, u_2} : ∀ {Ω : Type u_1} {ι : Type u_2}
  [inst : MeasurableSpace.{u_1} Ω] (μ : @MeasureTheory.Measure.{u_1} Ω inst)
  [@MeasureTheory.IsProbabilityMeasure.{u_1} Ω inst μ] (X : ι → Ω → Real),
  (∀ (i : ι), @Measurable.{u_1, 0} Ω Real inst Real.measurableSpace (X i)) →
    (∀ (i : ι) (ω : Ω),
        Or (@Eq.{1} Real (X i ω) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (@Eq.{1} Real (X i ω) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
      @ProbabilityTheory.iIndepFun.{u_1, u_2, 0} Ω ι inst (fun x => Real) (fun x => Real.measurableSpace) X μ →
        ∀ (indices : Finset.{u_2} ι) (t : Real),
          @MeasureTheory.Integrable.{0, u_1} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@SeminormedAddGroup.toContinuousENorm.{0} Real
              (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                      (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))))
            Ω inst
            (fun ω =>
              Real.exp
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t ((∑ i ∈ indices, X i) ω)))
            μ :=
⋯
'Luce.Section6.bernoulli_sum_exp_integrable' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### bernoulli_relative_upper_tail

```lean
theorem Luce.Section6.bernoulli_relative_upper_tail.{u_1, u_2} : ∀ {Ω : Type u_1} {ι : Type u_2}
  [inst : MeasurableSpace.{u_1} Ω] (μ : @MeasureTheory.Measure.{u_1} Ω inst)
  [@MeasureTheory.IsProbabilityMeasure.{u_1} Ω inst μ] (X : ι → Ω → Real),
  (∀ (i : ι), @Measurable.{u_1, 0} Ω Real inst Real.measurableSpace (X i)) →
    (∀ (i : ι) (ω : Ω),
        Or (@Eq.{1} Real (X i ω) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (@Eq.{1} Real (X i ω) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
      @ProbabilityTheory.iIndepFun.{u_1, u_2, 0} Ω ι inst (fun x => Real) (fun x => Real.measurableSpace) X μ →
        ∀ (indices : Finset.{u_2} ι) {eps : Real},
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
            @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
              have m :=
                ∑ i ∈ indices,
                  @MeasureTheory.integral.{u_1, 0} Ω Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    inst μ fun ω => X i ω;
              @LE.le.{0} Real Real.instLE
                (@MeasureTheory.Measure.real.{u_1} Ω inst μ
                  (@Set.ofPred.{u_1} Ω fun ω =>
                    @LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
                        m)
                      (∑ i ∈ indices, X i ω)))
                (Real.exp
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          eps (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      m)
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯)))) :=
⋯
'Luce.Section6.bernoulli_relative_upper_tail' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### bernoulli_relative_lower_tail

```lean
theorem Luce.Section6.bernoulli_relative_lower_tail.{u_1, u_2} : ∀ {Ω : Type u_1} {ι : Type u_2}
  [inst : MeasurableSpace.{u_1} Ω] (μ : @MeasureTheory.Measure.{u_1} Ω inst)
  [@MeasureTheory.IsProbabilityMeasure.{u_1} Ω inst μ] (X : ι → Ω → Real),
  (∀ (i : ι), @Measurable.{u_1, 0} Ω Real inst Real.measurableSpace (X i)) →
    (∀ (i : ι) (ω : Ω),
        Or (@Eq.{1} Real (X i ω) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (@Eq.{1} Real (X i ω) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
      @ProbabilityTheory.iIndepFun.{u_1, u_2, 0} Ω ι inst (fun x => Real) (fun x => Real.measurableSpace) X μ →
        ∀ (indices : Finset.{u_2} ι) {eps : Real},
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
            @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
              have m :=
                ∑ i ∈ indices,
                  @MeasureTheory.integral.{u_1, 0} Ω Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    inst μ fun ω => X i ω;
              @LE.le.{0} Real Real.instLE
                (@MeasureTheory.Measure.real.{u_1} Ω inst μ
                  (@Set.ofPred.{u_1} Ω fun ω =>
                    @LE.le.{0} Real Real.instLE (∑ i ∈ indices, X i ω)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
                        m)))
                (Real.exp
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          eps (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      m)
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯)))) :=
⋯
'Luce.Section6.bernoulli_relative_lower_tail' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_arrival_relative_tails

```lean
theorem Luce.Section6.deleted_arrival_relative_tails : ∀ {n : Nat} (w : Luce.Weights n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (removed : Finset.{0} (Fin n)) {t eps : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
          @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            And
              (@LE.le.{0} Real Real.instLE
                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                  (@Luce.exponentialRace n w)
                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                    @LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedG n w removed t)))
                      (∑
                        i ∈
                          @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
                        @Luce.Section6.clockArrivalIndicator n t i old)))
                (Real.exp
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          eps (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedG n w removed t)))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯)))))
              (@LE.le.{0} Real Real.instLE
                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                  (@Luce.exponentialRace n w)
                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                    @LE.le.{0} Real Real.instLE
                      (∑
                        i ∈
                          @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
                        @Luce.Section6.clockArrivalIndicator n t i old)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedG n w removed t)))))
                (Real.exp
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          eps (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedG n w removed t)))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯))))) :=
⋯
'Luce.Section6.deleted_arrival_relative_tails' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_survivor_relative_tails

```lean
theorem Luce.Section6.deleted_survivor_relative_tails : ∀ {n : Nat} (w : Luce.Weights n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (removed : Finset.{0} (Fin n)) {t eps : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
          @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            And
              (@LE.le.{0} Real Real.instLE
                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                  (@Luce.exponentialRace n w)
                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                    @LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedH n w removed t)))
                      (∑
                        i ∈
                          @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
                        @Luce.clockSurvivalIndicator n t i old)))
                (Real.exp
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          eps (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedH n w removed t)))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯)))))
              (@LE.le.{0} Real Real.instLE
                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                  (@Luce.exponentialRace n w)
                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                    @LE.le.{0} Real Real.instLE
                      (∑
                        i ∈
                          @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
                        @Luce.clockSurvivalIndicator n t i old)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedH n w removed t)))))
                (Real.exp
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          eps (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedH n w removed t)))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯))))) :=
⋯
'Luce.Section6.deleted_survivor_relative_tails' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_arrivals_le_beforeCount_of_lt

```lean
theorem Luce.Section6.deleted_arrivals_le_beforeCount_of_lt : ∀ {n : Nat} (removed : Finset.{0} (Fin n))
  (old : Fin n → Real) {t T : Real},
  @LT.lt.{0} Real Real.instLT t T →
    @LE.le.{0} Real Real.instLE
      (∑
        i ∈
          @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
        @Luce.Section6.clockArrivalIndicator n t i old)
      (@Nat.cast.{0} Real Real.instNatCast (@Luce.deletedBeforeCount n removed old T)) :=
⋯
'Luce.Section6.deleted_arrivals_le_beforeCount_of_lt' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_gapStart_gt_imp_arrivals_le

```lean
theorem Luce.Section6.deleted_gapStart_gt_imp_arrivals_le : ∀ {n : Nat} (removed : Finset.{0} (Fin n))
  (old : Fin n → Real),
  @Function.Injective.{1, 1} (Fin n) Real old →
    ∀
      (q :
        Fin
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
      {t : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @LT.lt.{0} Real Real.instLT t
            (@Luce.raceGapStart
              (@Finset.card.{0} (Fin n)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
              (@Luce.compactDeletedClocks n removed old) q) →
          @LE.le.{0} Real Real.instLE
            (∑
              i ∈
                @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
              @Luce.Section6.clockArrivalIndicator n t i old)
            (@Nat.cast.{0} Real Real.instNatCast
              (@Fin.val
                (@Finset.card.{0} (Fin n)
                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                q)) :=
⋯
'Luce.Section6.deleted_gapStart_gt_imp_arrivals_le' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_gap_start_relative_early_arrival

```lean
theorem Luce.Section6.deleted_gap_start_relative_early_arrival : ∀ {n : Nat} (w : Luce.Weights n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (removed : Finset.{0} (Fin n))
      (q :
        Fin
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
      {t eps : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
          @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            @LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedG n w removed t)))
                (@Nat.cast.{0} Real Real.instNatCast
                  (@Fin.val
                    (@Finset.card.{0} (Fin n)
                      (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                        (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                    q)) →
              @LE.le.{0} Real Real.instLE
                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                  (@Luce.exponentialRace n w)
                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                    @LT.lt.{0} Real Real.instLT
                      (@Luce.raceGapStart
                        (@Finset.card.{0} (Fin n)
                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                        (@Luce.compactDeletedClocks n removed old) q)
                      t))
                (Real.exp
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          eps (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedG n w removed t)))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯)))) :=
⋯
'Luce.Section6.deleted_gap_start_relative_early_arrival' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### deleted_gap_start_relative_late_arrival

```lean
theorem Luce.Section6.deleted_gap_start_relative_late_arrival : ∀ {n : Nat} (w : Luce.Weights n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (removed : Finset.{0} (Fin n))
      (q :
        Fin
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
      {t eps : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
          @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            @LE.le.{0} Real Real.instLE
                (@Nat.cast.{0} Real Real.instNatCast
                  (@Fin.val
                    (@Finset.card.{0} (Fin n)
                      (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                        (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                    q))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedG n w removed t))) →
              @LE.le.{0} Real Real.instLE
                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                  (@Luce.exponentialRace n w)
                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                    @LT.lt.{0} Real Real.instLT t
                      (@Luce.raceGapStart
                        (@Finset.card.{0} (Fin n)
                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                        (@Luce.compactDeletedClocks n removed old) q)))
                (Real.exp
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          eps (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedG n w removed t)))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯)))) :=
⋯
'Luce.Section6.deleted_gap_start_relative_late_arrival' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### deleted_arrivals_add_survivors

```lean
theorem Luce.Section6.deleted_arrivals_add_survivors : ∀ {n : Nat} (removed : Finset.{0} (Fin n)) (old : Fin n → Real)
  (t : Real),
  @Eq.{1} Real
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (∑
        i ∈
          @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
        @Luce.Section6.clockArrivalIndicator n t i old)
      (∑
        i ∈
          @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
        @Luce.clockSurvivalIndicator n t i old))
    (@Nat.cast.{0} Real Real.instNatCast
      (@Finset.card.{0} (Fin n)
        (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
          (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))) :=
⋯
'Luce.Section6.deleted_arrivals_add_survivors' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_gap_start_relative_early_survivor

```lean
theorem Luce.Section6.deleted_gap_start_relative_early_survivor : ∀ {n : Nat} (w : Luce.Weights n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (removed : Finset.{0} (Fin n))
      (q :
        Fin
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
      {t eps : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
          @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            @LE.le.{0} Real Real.instLE
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Finset.card.{0} (Fin n)
                      (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                        (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Fin.val
                      (@Finset.card.{0} (Fin n)
                        (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                          (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                      q)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedH n w removed t))) →
              @LE.le.{0} Real Real.instLE
                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                  (@Luce.exponentialRace n w)
                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                    @LT.lt.{0} Real Real.instLT
                      (@Luce.raceGapStart
                        (@Finset.card.{0} (Fin n)
                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                        (@Luce.compactDeletedClocks n removed old) q)
                      t))
                (Real.exp
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          eps (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedH n w removed t)))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯)))) :=
⋯
'Luce.Section6.deleted_gap_start_relative_early_survivor' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### deleted_gap_start_relative_late_survivor

```lean
theorem Luce.Section6.deleted_gap_start_relative_late_survivor : ∀ {n : Nat} (w : Luce.Weights n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (removed : Finset.{0} (Fin n))
      (q :
        Fin
          (@Finset.card.{0} (Fin n)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
              (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
      {t eps : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
          @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            @LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedH n w removed t)))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Finset.card.{0} (Fin n)
                      (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                        (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Fin.val
                      (@Finset.card.{0} (Fin n)
                        (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                          (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                      q))) →
              @LE.le.{0} Real Real.instLE
                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                  (@Luce.exponentialRace n w)
                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                    @LT.lt.{0} Real Real.instLT t
                      (@Luce.raceGapStart
                        (@Finset.card.{0} (Fin n)
                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                        (@Luce.compactDeletedClocks n removed old) q)))
                (Real.exp
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Neg.neg.{0} Real Real.instNeg
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          eps (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast n) (@Luce.Section6.deletedH n w removed t)))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯)))) :=
⋯
'Luce.Section6.deleted_gap_start_relative_late_survivor' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### scaled_deletion_error

```lean
theorem Luce.Section6.scaled_deletion_error : ∀ {n r : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ {A B : Real},
      @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) A B))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast r) (@Nat.cast.{0} Real Real.instNatCast n)) →
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast n) A)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast n) B)))
          (@Nat.cast.{0} Real Real.instNatCast r) :=
⋯
'Luce.Section6.scaled_deletion_error' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### PowerProfile.left_deleted_quantile_separation

```lean
theorem Luce.Section6.PowerProfile.left_deleted_quantile_separation : ∀ {f : Real → Real}
  {right : Luce.Section6.EndpointBehavior} {c alpha eta : Real},
  Luce.Section6.PowerProfile f (Luce.Section6.EndpointBehavior.power c alpha eta) right →
    ∃ a delta M,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
        (And (@LE.le.{0} Real Real.instLE a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              delta)
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                M)
              (∀ (grid : Luce.Section6.SamplingGrid) (w : Luce.WeightArray),
                Luce.Section6.SampledRates grid w f →
                  ∀ (n m r : Nat),
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
                      @LT.lt.{0} Nat instLTNat m n →
                        @LE.le.{0} Real Real.instLE M (@Nat.cast.{0} Real Real.instNatCast m) →
                          @LT.lt.{0} Real Real.instLT
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@Nat.cast.{0} Real Real.instNatCast m) (@Nat.cast.{0} Real Real.instNatCast n))
                              delta →
                            ∀ (removed : Finset.{0} (Fin n)),
                              @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin n) removed) r →
                                ∀ (u : Real),
                                  @LT.lt.{0} Real Real.instLT
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u →
                                    @LE.le.{0} Real Real.instLE u
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯))) →
                                      And
                                        (@LE.le.{0} Real Real.instLE
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@Nat.cast.{0} Real Real.instNatCast n)
                                            (@Luce.Section6.deletedG n (w n) removed
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                    (@One.toOfNat1.{0} Real Real.instOne))
                                                  u)
                                                (@Luce.Section6.leftQuantileTime n (w n) m))))
                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                              (@Nat.cast.{0} Real Real.instNatCast m)
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
                                                  u)
                                                (@Nat.cast.{0} Real Real.instNatCast m)))
                                            (@Nat.cast.{0} Real Real.instNatCast r)))
                                        (@LE.le.{0} Real Real.instLE
                                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                              (@Nat.cast.{0} Real Real.instNatCast m)
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
                                                  u)
                                                (@Nat.cast.{0} Real Real.instNatCast m)))
                                            (@Nat.cast.{0} Real Real.instNatCast r))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@Nat.cast.{0} Real Real.instNatCast n)
                                            (@Luce.Section6.deletedG n (w n) removed
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                    (@One.toOfNat1.{0} Real Real.instOne))
                                                  u)
                                                (@Luce.Section6.leftQuantileTime n (w n) m))))))))) :=
⋯
'Luce.Section6.PowerProfile.left_deleted_quantile_separation' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### PowerProfile.right_deleted_quantile_separation

```lean
theorem Luce.Section6.PowerProfile.right_deleted_quantile_separation : ∀ {f : Real → Real}
  {left : Luce.Section6.EndpointBehavior} {c beta eta : Real},
  Luce.Section6.PowerProfile f left (Luce.Section6.EndpointBehavior.power c beta eta) →
    ∃ a delta M,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
        (And (@LE.le.{0} Real Real.instLE a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              delta)
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                M)
              (∀ (grid : Luce.Section6.SamplingGrid) (w : Luce.WeightArray),
                Luce.Section6.SampledRates grid w f →
                  ∀ (n m r : Nat),
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
                      @LT.lt.{0} Nat instLTNat m n →
                        @LE.le.{0} Real Real.instLE M (@Nat.cast.{0} Real Real.instNatCast m) →
                          @LT.lt.{0} Real Real.instLT
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@Nat.cast.{0} Real Real.instNatCast m) (@Nat.cast.{0} Real Real.instNatCast n))
                              delta →
                            ∀ (removed : Finset.{0} (Fin n)),
                              @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin n) removed) r →
                                ∀ (u : Real),
                                  @LT.lt.{0} Real Real.instLT
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u →
                                    @LE.le.{0} Real Real.instLE u
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯))) →
                                      And
                                        (@LE.le.{0} Real Real.instLE
                                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                              (@Nat.cast.{0} Real Real.instNatCast m)
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
                                                  u)
                                                (@Nat.cast.{0} Real Real.instNatCast m)))
                                            (@Nat.cast.{0} Real Real.instNatCast r))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@Nat.cast.{0} Real Real.instNatCast n)
                                            (@Luce.Section6.deletedH n (w n) removed
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                    (@One.toOfNat1.{0} Real Real.instOne))
                                                  u)
                                                (@Luce.Section6.rightQuantileTime n (w n) m)))))
                                        (@LE.le.{0} Real Real.instLE
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@Nat.cast.{0} Real Real.instNatCast n)
                                            (@Luce.Section6.deletedH n (w n) removed
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                    (@One.toOfNat1.{0} Real Real.instOne))
                                                  u)
                                                (@Luce.Section6.rightQuantileTime n (w n) m))))
                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                              (@Nat.cast.{0} Real Real.instNatCast m)
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
                                                  u)
                                                (@Nat.cast.{0} Real Real.instNatCast m)))
                                            (@Nat.cast.{0} Real Real.instNatCast r))))))) :=
⋯
'Luce.Section6.PowerProfile.right_deleted_quantile_separation' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### relative_mean_separation

```lean
theorem Luce.Section6.relative_mean_separation : ∀ {m v R q low high : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) m →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) v →
      @LE.le.{0} Real Real.instLE v (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @LE.le.{0} Real Real.instLE R
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) v m)
              (@OfNat.ofNat.{0} Real (nat_lit 8) (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast ⋯))) →
          @LE.le.{0} Real Real.instLE
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) q m))
              R →
            @LE.le.{0} Real Real.instLE low
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) m
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) v m))
                  R) →
              @LE.le.{0} Real Real.instLE
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) m
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) v m))
                    R)
                  high →
                And
                  (@LE.le.{0} Real Real.instLE
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) v
                          (@OfNat.ofNat.{0} Real (nat_lit 8)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast ⋯))))
                      low)
                    q)
                  (@LE.le.{0} Real Real.instLE q
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) v
                          (@OfNat.ofNat.{0} Real (nat_lit 8)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast ⋯))))
                      high)) :=
⋯
'Luce.Section6.relative_mean_separation' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### PowerProfile.left_gap_quantile_window

```lean
theorem Luce.Section6.PowerProfile.left_gap_quantile_window : ∀ {f : Real → Real}
  {right : Luce.Section6.EndpointBehavior} {c alpha eta : Real},
  Luce.Section6.PowerProfile f (Luce.Section6.EndpointBehavior.power c alpha eta) right →
    ∃ a delta M,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
        (And (@LE.le.{0} Real Real.instLE a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              delta)
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                M)
              (∀ (grid : Luce.Section6.SamplingGrid) (w : Luce.WeightArray),
                Luce.Section6.SampledRates grid w f →
                  ∀ (n m r : Nat),
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
                      @LT.lt.{0} Nat instLTNat m n →
                        @LE.le.{0} Real Real.instLE M (@Nat.cast.{0} Real Real.instNatCast m) →
                          @LT.lt.{0} Real Real.instLT
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@Nat.cast.{0} Real Real.instNatCast m) (@Nat.cast.{0} Real Real.instNatCast n))
                              delta →
                            ∀ (removed : Finset.{0} (Fin n)),
                              @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin n) removed) r →
                                ∀
                                  (q :
                                    Fin
                                      (@Finset.card.{0} (Fin n)
                                        (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                                          (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                                          (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))),
                                  @LE.le.{0} Real Real.instLE
                                      (@abs.{0} Real Real.lattice Real.instAddGroup
                                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                          (@Nat.cast.{0} Real Real.instNatCast
                                            (@Fin.val
                                              (@Finset.card.{0} (Fin n)
                                                (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                                                  (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                                                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                                              q))
                                          (@Nat.cast.{0} Real Real.instNatCast m)))
                                      (@Nat.cast.{0} Real Real.instNatCast r) →
                                    ∀ (u : Real),
                                      @LT.lt.{0} Real Real.instLT
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                          u →
                                        @LE.le.{0} Real Real.instLE u
                                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯))) →
                                          @LE.le.{0} Real Real.instLE
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@OfNat.ofNat.{0} Real (nat_lit 8)
                                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast ⋯))
                                                (@Nat.cast.{0} Real Real.instNatCast r))
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
                                                  u)
                                                (@Nat.cast.{0} Real Real.instNatCast m)) →
                                            have lo :=
                                              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                    (@One.toOfNat1.{0} Real Real.instOne))
                                                  u)
                                                (@Luce.Section6.leftQuantileTime n (w n) m);
                                            have hi :=
                                              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                    (@One.toOfNat1.{0} Real Real.instOne))
                                                  u)
                                                (@Luce.Section6.leftQuantileTime n (w n) m);
                                            And
                                              (@LE.le.{0} Real Real.instLE
                                                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                                                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a =>
                                                    Real.measurableSpace)
                                                  (@Luce.exponentialRace n (w n))
                                                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                                                    @LT.lt.{0} Real Real.instLT
                                                      (@Luce.raceGapStart
                                                        (@Finset.card.{0} (Fin n)
                                                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                                                            (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                                                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                                                        (@Luce.compactDeletedClocks n removed old) q)
                                                      lo))
                                                (Real.exp
                                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                    (@instHDiv.{0} Real
                                                      (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@Neg.neg.{0} Real Real.instNeg
                                                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                          (@instHPow.{0, 0} Real Nat
                                                            (@NPow.toPow.{0} Real
                                                              (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                            (@instHDiv.{0} Real
                                                              (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul) a u)
                                                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                                                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8)
                                                                Real.instNatCast ⋯)))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (@Nat.cast.{0} Real Real.instNatCast n)
                                                        (@Luce.Section6.deletedG n (w n) removed lo)))
                                                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯)))))
                                              (@LE.le.{0} Real Real.instLE
                                                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                                                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a =>
                                                    Real.measurableSpace)
                                                  (@Luce.exponentialRace n (w n))
                                                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                                                    @LT.lt.{0} Real Real.instLT hi
                                                      (@Luce.raceGapStart
                                                        (@Finset.card.{0} (Fin n)
                                                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                                                            (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                                                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                                                        (@Luce.compactDeletedClocks n removed old) q)))
                                                (Real.exp
                                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                    (@instHDiv.{0} Real
                                                      (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@Neg.neg.{0} Real Real.instNeg
                                                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                          (@instHPow.{0, 0} Real Nat
                                                            (@NPow.toPow.{0} Real
                                                              (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                            (@instHDiv.{0} Real
                                                              (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul) a u)
                                                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                                                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8)
                                                                Real.instNatCast ⋯)))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (@Nat.cast.{0} Real Real.instNatCast n)
                                                        (@Luce.Section6.deletedG n (w n) removed hi)))
                                                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                                        ⋯))))))))) :=
⋯
'Luce.Section6.PowerProfile.left_gap_quantile_window' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### PowerProfile.right_gap_quantile_window

```lean
theorem Luce.Section6.PowerProfile.right_gap_quantile_window : ∀ {f : Real → Real}
  {left : Luce.Section6.EndpointBehavior} {c beta eta : Real},
  Luce.Section6.PowerProfile f left (Luce.Section6.EndpointBehavior.power c beta eta) →
    ∃ a delta M,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
        (And (@LE.le.{0} Real Real.instLE a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              delta)
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                M)
              (∀ (grid : Luce.Section6.SamplingGrid) (w : Luce.WeightArray),
                Luce.Section6.SampledRates grid w f →
                  ∀ (n m r : Nat),
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
                      @LT.lt.{0} Nat instLTNat m n →
                        @LE.le.{0} Real Real.instLE M (@Nat.cast.{0} Real Real.instNatCast m) →
                          @LT.lt.{0} Real Real.instLT
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@Nat.cast.{0} Real Real.instNatCast m) (@Nat.cast.{0} Real Real.instNatCast n))
                              delta →
                            ∀ (removed : Finset.{0} (Fin n)),
                              @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin n) removed) r →
                                ∀
                                  (q :
                                    Fin
                                      (@Finset.card.{0} (Fin n)
                                        (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                                          (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                                          (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))),
                                  @LE.le.{0} Real Real.instLE
                                      (@abs.{0} Real Real.lattice Real.instAddGroup
                                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                            (@Nat.cast.{0} Real Real.instNatCast
                                              (@Finset.card.{0} (Fin n)
                                                (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                                                  (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                                                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed)))
                                            (@Nat.cast.{0} Real Real.instNatCast
                                              (@Fin.val
                                                (@Finset.card.{0} (Fin n)
                                                  (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                                                    (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                                                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                                                q)))
                                          (@Nat.cast.{0} Real Real.instNatCast m)))
                                      (@Nat.cast.{0} Real Real.instNatCast r) →
                                    ∀ (u : Real),
                                      @LT.lt.{0} Real Real.instLT
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                          u →
                                        @LE.le.{0} Real Real.instLE u
                                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯))) →
                                          @LE.le.{0} Real Real.instLE
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@OfNat.ofNat.{0} Real (nat_lit 8)
                                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast ⋯))
                                                (@Nat.cast.{0} Real Real.instNatCast r))
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
                                                  u)
                                                (@Nat.cast.{0} Real Real.instNatCast m)) →
                                            have lo :=
                                              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                    (@One.toOfNat1.{0} Real Real.instOne))
                                                  u)
                                                (@Luce.Section6.rightQuantileTime n (w n) m);
                                            have hi :=
                                              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                    (@One.toOfNat1.{0} Real Real.instOne))
                                                  u)
                                                (@Luce.Section6.rightQuantileTime n (w n) m);
                                            And
                                              (@LE.le.{0} Real Real.instLE
                                                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                                                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a =>
                                                    Real.measurableSpace)
                                                  (@Luce.exponentialRace n (w n))
                                                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                                                    @LT.lt.{0} Real Real.instLT
                                                      (@Luce.raceGapStart
                                                        (@Finset.card.{0} (Fin n)
                                                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                                                            (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                                                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                                                        (@Luce.compactDeletedClocks n removed old) q)
                                                      lo))
                                                (Real.exp
                                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                    (@instHDiv.{0} Real
                                                      (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@Neg.neg.{0} Real Real.instNeg
                                                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                          (@instHPow.{0, 0} Real Nat
                                                            (@NPow.toPow.{0} Real
                                                              (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                            (@instHDiv.{0} Real
                                                              (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul) a u)
                                                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                                                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8)
                                                                Real.instNatCast ⋯)))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (@Nat.cast.{0} Real Real.instNatCast n)
                                                        (@Luce.Section6.deletedH n (w n) removed lo)))
                                                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯)))))
                                              (@LE.le.{0} Real Real.instLE
                                                (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                                                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a =>
                                                    Real.measurableSpace)
                                                  (@Luce.exponentialRace n (w n))
                                                  (@Set.ofPred.{0} (Fin n → Real) fun old =>
                                                    @LT.lt.{0} Real Real.instLT hi
                                                      (@Luce.raceGapStart
                                                        (@Finset.card.{0} (Fin n)
                                                          (@SDiff.sdiff.{0} (Finset.{0} (Fin n))
                                                            (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                                                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed))
                                                        (@Luce.compactDeletedClocks n removed old) q)))
                                                (Real.exp
                                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                    (@instHDiv.{0} Real
                                                      (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@Neg.neg.{0} Real Real.instNeg
                                                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                          (@instHPow.{0, 0} Real Nat
                                                            (@NPow.toPow.{0} Real
                                                              (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                            (@instHDiv.{0} Real
                                                              (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul) a u)
                                                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                                                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8)
                                                                Real.instNatCast ⋯)))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (@Nat.cast.{0} Real Real.instNatCast n)
                                                        (@Luce.Section6.deletedH n (w n) removed hi)))
                                                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                                        ⋯))))))))) :=
⋯
'Luce.Section6.PowerProfile.right_gap_quantile_window' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### sorted_gap_left_displacement

```lean
theorem Luce.Section6.sorted_gap_left_displacement : ∀ {n s r : Nat},
  @LE.le.{0} Nat instLENat s r →
    ∀ (j : Fin s → Fin n),
      @Function.Injective.{1, 1} (Fin s) (Fin n) j →
        ∀ (e : Fin s),
          @LE.le.{0} Real Real.instLE
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@Nat.cast.{0} Real Real.instNatCast (@Luce.sortedMarkedGapIndex n s j e))
                (@Nat.cast.{0} Real Real.instNatCast
                  (@Luce.Section6.cornerDistance Luce.Section6.Corner.left n
                    (j
                      (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (fun x => Fin s)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (Fin s)
                          (@Equiv.instEquivLike.{1, 1} (Fin s) (Fin s)))
                        (@Tuple.sort.{0} s (Fin n) (@Fin.instLinearOrder n) j) e))))))
            (@Nat.cast.{0} Real Real.instNatCast r) :=
⋯
'Luce.Section6.sorted_gap_left_displacement' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### sorted_gap_right_displacement

```lean
theorem Luce.Section6.sorted_gap_right_displacement : ∀ {n s r : Nat},
  @LE.le.{0} Nat instLENat s r →
    ∀ (u j : Fin s → Fin n),
      @Function.Injective.{1, 1} (Fin s) (Fin n) u →
        @Function.Injective.{1, 1} (Fin s) (Fin n) j →
          ∀ (e : Fin s),
            @LE.le.{0} Real Real.instLE
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Finset.card.{0} (Fin n)
                        (@SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                          (@Finset.univ.{0} (Fin n) (Fin.fintype n))
                          (@Finset.image.{0, 0} (Fin s) (Fin n) (instDecidableEqFin n)
                            (@Function.comp.{1, 1, 1} (Fin s) (Fin s) (Fin n) u
                              (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (fun x => Fin s)
                                (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (Fin s)
                                  (@Equiv.instEquivLike.{1, 1} (Fin s) (Fin s)))
                                (@Tuple.sort.{0} s (Fin n) (@Fin.instLinearOrder n) j)))
                            (@Finset.univ.{0} (Fin s) (Fin.fintype s))))))
                    (@Nat.cast.{0} Real Real.instNatCast (@Luce.sortedMarkedGapIndex n s j e)))
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n
                      (j
                        (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (fun x => Fin s)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} (Fin s)) (Fin s) (Fin s)
                            (@Equiv.instEquivLike.{1, 1} (Fin s) (Fin s)))
                          (@Tuple.sort.{0} s (Fin n) (@Fin.instLinearOrder n) j) e))))))
              (@Nat.cast.{0} Real Real.instNatCast r) :=
⋯
'Luce.Section6.sorted_gap_right_displacement' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### survival_indicator_memLp_two

```lean
theorem Luce.Section6.survival_indicator_memLp_two : ∀ {n : Nat} (w : Luce.Weights n) (t : Real) (i : Fin n),
  @MeasureTheory.MemLp.{0, 0} (Fin n → Real) Real
    (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
    (@ContinuousENorm.toENorm.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real
        (@PseudoMetricSpace.toUniformSpace.{0} Real
          (@SeminormedAddGroup.toPseudoMetricSpace.{0} Real
            (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))))))
      (@SeminormedAddGroup.toContinuousENorm.{0} Real
        (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@Luce.clockSurvivalIndicator n t i)
    (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        ⋯))
    (@Luce.exponentialRace n w) :=
⋯
'Luce.Section6.survival_indicator_memLp_two' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### survival_indicator_variance_le_mean

```lean
theorem Luce.Section6.survival_indicator_variance_le_mean : ∀ {n : Nat} (w : Luce.Weights n) (t : Real) (i : Fin n),
  @LE.le.{0} Real Real.instLE
    (@ProbabilityTheory.variance.{0} (Fin n → Real)
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
      (@Luce.clockSurvivalIndicator n t i) (@Luce.exponentialRace n w))
    (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace) (@Luce.exponentialRace n w)
      fun old => @Luce.clockSurvivalIndicator n t i old) :=
⋯
'Luce.Section6.survival_indicator_variance_le_mean' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_remaining_weight_variance

```lean
theorem Luce.Section6.deleted_remaining_weight_variance : ∀ {n : Nat} (w : Luce.Weights n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (removed : Finset.{0} (Fin n)) {t : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @LE.le.{0} Real Real.instLE
          (@ProbabilityTheory.variance.{0} (Fin n → Real)
            (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
            (fun old =>
              ∑
                i ∈
                  @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
                @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Luce.Weights.rate n w i)
                  (@Luce.clockSurvivalIndicator n t i old))
            (@Luce.exponentialRace n w))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast n)
            (@Luce.Section6.deletedD n w removed (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)) :=
⋯
'Luce.Section6.deleted_remaining_weight_variance' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_remaining_weight_mean

```lean
theorem Luce.Section6.deleted_remaining_weight_mean : ∀ {n : Nat} (w : Luce.Weights n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (removed : Finset.{0} (Fin n)) {t : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @Eq.{1} Real
          (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
            (@Luce.exponentialRace n w) fun old =>
            ∑
              i ∈
                @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                  (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Luce.Weights.rate n w i)
                (@Luce.clockSurvivalIndicator n t i old))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast n)
            (@Luce.Section6.deletedD n w removed (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) t)) :=
⋯
'Luce.Section6.deleted_remaining_weight_mean' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### deleted_remaining_weight_chebyshev

```lean
theorem Luce.Section6.deleted_remaining_weight_chebyshev : ∀ {n : Nat} (w : Luce.Weights n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (removed : Finset.{0} (Fin n)) {t eps : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
          @LE.le.{0} Real Real.instLE
            (@MeasureTheory.Measure.real.{0} (Fin n → Real)
              (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
              (@Luce.exponentialRace n w)
              (@Set.ofPred.{0} (Fin n → Real) fun old =>
                @LE.le.{0} Real Real.instLE eps
                  (@abs.{0} Real Real.lattice Real.instAddGroup
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (∑
                        i ∈
                          @SDiff.sdiff.{0} (Finset.{0} (Fin n)) (@Finset.instSDiff.{0} (Fin n) (instDecidableEqFin n))
                            (@Finset.univ.{0} (Fin n) (Fin.fintype n)) removed,
                        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Luce.Weights.rate n w i)
                          (@Luce.clockSurvivalIndicator n t i old))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@Luce.Section6.deletedD n w removed
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) t))))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast n)
                (@Luce.Section6.deletedD n w removed (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) eps
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) :=
⋯
'Luce.Section6.deleted_remaining_weight_chebyshev' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## Exact closed target (unchanged; no proof claimed)

```lean
import Luce.Section6LocalKernelDefinitions
import Luce.Section5GhostCylinder
import Luce.Section6Lemma64Contract

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace Luce.Section6.Proposition65Contract

/-- Closed target for the complete joint local insertion law. Every
configuration premise is a literal domain restriction in Proposition 6.5. -/
def localLaw : Prop :=
  ∀ (f : ℝ → ℝ) (left right : EndpointBehavior), PowerProfile f left right →
  ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
  ∀ r : ℕ, ∃ (h0 : ℕ) (delta v d kappa C : ℝ),
    1 ≤ h0 ∧ 0 < delta ∧ delta < 1 ∧ 0 < v ∧ v ≤ 1 ∧
    0 < d ∧ 0 < kappa ∧ 0 < C ∧
    (∀ (n s : ℕ), s ≤ r → ∀ (side : Fin s → Corner) (u j : Fin s → Fin n),
      Injective u → Injective j →
      (∀ e, (cornerBehavior left right (side e)).active) →
      (∀ e, h0 ≤ cornerDistance (side e) (u e) ∧ h0 ≤ cornerDistance (side e) (j e)) →
      (∀ e, (cornerDistance (side e) (u e) : ℝ) ≤ delta*(n : ℝ) ∧
        (cornerDistance (side e) (j e) : ℝ) ≤ delta*(n : ℝ)) →
      (∀ e, localCornerRatio (side e) (cornerBehavior left right (side e))
        (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e)) ≤
        (min (cornerDistance (side e) (u e) : ℝ) (cornerDistance (side e) (j e) : ℝ))^v) →
      (∀ e g, e ≠ g → 2*r < Nat.dist (j e).val (j g).val) →
      let err := |(exponentialRace (w n)).real {clocks | MarkedRankCylinder u j clocks} -
        ∏ e, localIdealKernel (side e) (cornerBehavior left right (side e))
          (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e))|
      let envelope := ∏ e, localEnvelopeKernel (side e) (cornerBehavior left right (side e)) d
        (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e))
      err ≤ C*envelope*(∑ e,
        ((min (cornerDistance (side e) (u e) : ℝ) (cornerDistance (side e) (j e) : ℝ))^(-kappa) +
        ((max (cornerDistance (side e) (u e) : ℝ) (cornerDistance (side e) (j e) : ℝ))/(n : ℝ))^kappa)) ∧
      (∀ A B : ℝ, 0 < A →
        (∀ e, A ≤ (cornerDistance (side e) (u e) : ℝ) ∧
          A ≤ (cornerDistance (side e) (j e) : ℝ) ∧
          (cornerDistance (side e) (u e) : ℝ) ≤ B ∧
          (cornerDistance (side e) (j e) : ℝ) ≤ B) →
        err ≤ C*(A^(-kappa)+(B/(n : ℝ))^kappa)*envelope))

/-- Preserve the full global matrix properties for all other configurations,
including adjacent ranks; the second component is a conclusion, not an input. -/
def proposition65 : Prop := localLaw ∧ Lemma64Contract.matrix

end Luce.Section6.Proposition65Contract
```

There is no main-theorem or contract-check axiom output: neither theorem has been declared.
The obligation ledger and command results are in section6-proposition65-audit.md.
