import Luce.EndpointExceptionalTheorem

/-! Closed statement and transitive axiom checks for Lemma 4.3 and
Corollary 4.7 of `fixed_points_sampled_profile.tex`. -/
noncomputable section
open Luce MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal BoundedContinuousFunction

-- The minimum is attained among precisely the candidate-deleted subsets
-- with m-1 elements; it is bounded above by every such subset total.
#check @deletedSmallestRateSum_attained
#check @deletedSmallestRateSum_le
#print deletedRateSubsets
#print deletedSmallestRateSum
#print slowLabelCharge

-- Depth one has no other surviving labels, including in a singleton row.
example {n : ℕ} (w : Weights (n+1)) : deletedSmallestRateSum w (Fin.last n) = 0 := by
  obtain ⟨s, _, hc, hs⟩ := deletedSmallestRateSum_attained w (Fin.last n)
  have hc0 : s.card = 0 := by simpa using hc
  rw [Finset.card_eq_zero.mp hc0] at hs
  simpa [Weights.total] using hs

example {n : ℕ} (w : Weights n) (k : Fin n) :
    (exponentialRace w).real {e | raceRank e k = k.val+1} ≤
      w.rate k / (w.rate k + deletedSmallestRateSum w k) :=
  race_individual_slow_label_charge w k

-- Freeze the raw combined condition, instead of assuming a buffered
-- estimate, a tail theorem, or finiteness of the limiting intensity.
example (w : WeightArray) (E : ∀ n, Finset (Fin n))
    (hnorm : NormalizedWeights w)
    (h : Tendsto (fun J : ℕ => limsup (fun n : ℕ =>
      (∑' j : ℕ, if J ≤ j then
        if hs : (terminalShell n j \ E n).Nonempty then
          ENNReal.ofReal (Real.exp
            (-(((terminalShell n j \ E n).image (w n).rate).min' (hs.image _)) * (j : ℝ)))
        else 0
      else 0) +
      ∑ k ∈ (Finset.univ.filter fun k : Fin n =>
        (terminalDepth k : ℝ) ≤ (n : ℝ) * Real.exp (-(J : ℝ))).filter (fun k => k ∈ E n),
        ENNReal.ofReal ((w n).rate k /
          ((w n).rate k + deletedSmallestRateSum (w n) k))) atTop) atTop (𝓝 0)) :
    Tendsto (fun J : ℕ => limsup (fun n : ℕ =>
      ∫ e, (((Finset.univ.filter fun k : Fin n =>
        (terminalDepth k : ℝ) ≤ (n : ℝ) * Real.exp (-(J : ℝ))).filter
          fun k => raceRank e k = k.val+1).card : ℝ) ∂exponentialRace (w n)) atTop)
      atTop (𝓝 (0 : ℝ)) :=
  (corollary47_endpoint w E hnorm h).1

#print EndpointExceptionalAssumption
#print exceptionalTailCharge
#print terminalDepthExpectation
#check @individual_slow_label_charge
#check @corollary47_endpoint
#check @corollary47_epsilon
#check @corollary47
#check @corollary47_general
#check @exceptionalFullIntensity_projection

#print axioms deletedSmallestRateSum_attained
#print axioms deletedSmallestRateSum_le
#print axioms individual_slow_label_charge
#print axioms race_individual_slow_label_charge
#print axioms terminalDepthBlock_sum_eq_shells
#print axioms EndpointExceptionalAssumption.expectation_shells
#print axioms EndpointExceptionalAssumption.terminal_depth_limit
#print axioms corollary47_endpoint
#print axioms corollary47_epsilon
#print axioms corollary47
#print axioms corollary47_general
#print axioms exceptionalFullIntensity_projection
