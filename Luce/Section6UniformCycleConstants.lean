import Luce.Section6Lemma67Contract

noncomputable section
namespace Luce.Section6

/-- Finite families of estimates admit one positive constant, neighborhood,
and exponent, provided increasing the constant and decreasing the other two
preserves the estimate. Empty families are included. -/
theorem finite_uniform_cycle_constants {ι : Type*} [Fintype ι]
    (P : ι → ℝ → ℝ → ℝ → Prop)
    (h : ∀ i, ∃ C d q : ℝ, 0 < C ∧ 0 < d ∧ d < 1 ∧ 0 < q ∧ P i C d q)
    (hmono : ∀ i C d q C' d' q', 0 < C → 0 < C' → 0 < d' → 0 < q' →
      C ≤ C' → d' ≤ d → q' ≤ q → P i C d q → P i C' d' q') :
    ∃ C d q : ℝ, 0 < C ∧ 0 < d ∧ d < 1 ∧ 0 < q ∧ ∀ i, P i C d q := by
  classical
  have hs (s : Finset ι) :
      ∃ C d q : ℝ, 0 < C ∧ 0 < d ∧ d < 1 ∧ 0 < q ∧ ∀ i ∈ s, P i C d q := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, 1/2, 1, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨C, d, q, hC, hd, hd1, hq, hP⟩ := h i
      obtain ⟨D, e, r, hD, he, he1, hr, hQ⟩ := ih
      refine ⟨C+D, min d e, min q r, by positivity, lt_min hd he,
        (min_le_left _ _).trans_lt hd1, lt_min hq hr, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hmono j C d q _ _ _ hC (by positivity) (lt_min hd he) (lt_min hq hr)
          (by linarith) (min_le_left _ _) (min_le_left _ _) hP
      · exact hmono j D e r _ _ _ hD (by positivity) (lt_min hd he) (lt_min hq hr)
          (by linarith) (min_le_right _ _) (min_le_right _ _) (hQ j hj)
  obtain ⟨C, d, q, hC, hd, hd1, hq, hP⟩ := hs Finset.univ
  exact ⟨C, d, q, hC, hd, hd1, hq, fun i => hP i (Finset.mem_univ i)⟩

theorem endpointEstimates_mono67 {f : ℝ → ℝ} {k : ℕ} {side : Corner}
    {C d q C' d' q' : ℝ} (hC : 0 < C) (hC' : 0 < C')
    (hCC : C ≤ C') (hdd : d' ≤ d) (hqq : q' ≤ q)
    (h : Lemma67Contract.endpointEstimates f k side C d q) :
    Lemma67Contract.endpointEstimates f k side C' d' q' := by
  intro grid w hw
  obtain ⟨hroot, hdisc, hlog⟩ := h grid w hw
  refine ⟨?_, ?_, ?_⟩
  · intro n v hv
    exact (hroot n v (hv.trans hdd)).trans
      (div_le_div_of_nonneg_right hCC (Nat.cast_nonneg _))
  · intro n A B hA hAB hB
    exact (hdisc n A B hA hAB (hB.trans hdd)).trans hCC
  · intro n A B R hA hAB hB hR
    have ha : 0 < A := by linarith
    have ht : 0 ≤ 1+Real.log (B/A) := by
      have := Real.log_nonneg ((one_le_div ha).mpr hAB)
      linarith
    apply (hlog n A B R hA hAB (hB.trans hdd) hR).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right hCC ht)
      (Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg hqq))
      (Real.rpow_nonneg (by linarith) _) (mul_nonneg hC'.le ht)

end Luce.Section6
