import Luce.Section1Assumptions
import Luce.Section3EmpiricalRace

/-!
# Exact deterministic means in Section 3

The finite sums in `fixed_points.tex:670–679` are the integrals of the
actual step profiles from lines 218–220. The proof retains the half-open
cells, including the final endpoint, and computes their measures.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Luce

private lemma section3_cell_unique {n : ℕ} {i j : Fin n} {x : ℝ}
    (hi : (i.val : ℝ) / n < x ∧ x ≤ ((i.val : ℝ) + 1) / n)
    (hj : (j.val : ℝ) / n < x ∧ x ≤ ((j.val : ℝ) + 1) / n) : i = j := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hi₁ := (div_lt_iff₀ hn).mp hi.1
  have hi₂ := (le_div_iff₀ hn).mp hi.2
  have hj₁ := (div_lt_iff₀ hn).mp hj.1
  have hj₂ := (le_div_iff₀ hn).mp hj.2
  apply Fin.ext
  have h₁ : i.val < j.val + 1 := by exact_mod_cast (show (i.val : ℝ) < j.val + 1 by linarith)
  have h₂ : j.val < i.val + 1 := by exact_mod_cast (show (j.val : ℝ) < i.val + 1 by linarith)
  omega

/-- A kernel that vanishes at zero acts cellwise on the literal profile.
This requires no continuity or measurability of the kernel. -/
theorem comp_stepProfile_eq_sum (w : WeightArray) (n : ℕ) (φ : ℝ → ℝ)
    (hφ : φ 0 = 0) (x : ℝ) :
    φ (stepProfile w n x) = ∑ i : Fin n,
      if (i.val : ℝ) / n < x ∧ x ≤ ((i.val : ℝ) + 1) / n
      then φ ((w n).rate i) else 0 := by
  classical
  by_cases hx : ∃ i : Fin n, (i.val : ℝ) / n < x ∧ x ≤ ((i.val : ℝ) + 1) / n
  · obtain ⟨i, hi⟩ := hx
    have hoff (j : Fin n) (hji : j ≠ i) :
        ¬ ((j.val : ℝ) / n < x ∧ x ≤ ((j.val : ℝ) + 1) / n) :=
      fun hj => hji (section3_cell_unique hj hi)
    have hs : stepProfile w n x = (w n).rate i := by
      unfold stepProfile
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        simp [hoff j hji]
      · simp
    rw [hs, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      simp [hoff j hji]
    · simp
  · have hz (i : Fin n) : ¬ ((i.val : ℝ) / n < x ∧ x ≤ ((i.val : ℝ) + 1) / n) :=
      fun hi => hx ⟨i, hi⟩
    simp [stepProfile, hz, hφ]

/-- Every half-open profile cell has precisely its stated length under
Lebesgue measure restricted to `(0,1)`. -/
theorem section3_cell_real_measure {n : ℕ} (i : Fin n) :
    profileMeasure.real (Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)) = 1 / n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hs : Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n) ⊆ Ioc (0 : ℝ) 1 := by
    intro x hx
    constructor
    · exact (div_nonneg (Nat.cast_nonneg _) hn.le).trans_lt hx.1
    · exact hx.2.trans ((div_le_one hn).mpr hi)
  have hμ : profileMeasure = volume.restrict (Ioc (0 : ℝ) 1) := by
    exact Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [hμ, Measure.real, Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr hs]
  change volume.real _ = _
  rw [Real.volume_real_Ioc_of_le
    (div_le_div_of_nonneg_right (by linarith) hn.le)]
  ring

/-- The exact finite-cell integral underlying both means (670–679).
Even a nonmeasurable kernel has a measurable finite-valued composition here. -/
theorem integral_comp_stepProfile (w : WeightArray) (n : ℕ) (φ : ℝ → ℝ)
    (hφ : φ 0 = 0) :
    (∫ x, φ (stepProfile w n x) ∂profileMeasure) =
      (∑ i : Fin n, φ ((w n).rate i)) / n := by
  classical
  haveI : IsFiniteMeasure profileMeasure := by
    unfold profileMeasure
    infer_instance
  have hfun (i : Fin n) :
      (fun x : ℝ => if (i.val : ℝ) / n < x ∧ x ≤ ((i.val : ℝ) + 1) / n
        then φ ((w n).rate i) else 0) =
      (Ioc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)).indicator
        (fun _ => φ ((w n).rate i)) := by
    funext x
    simp only [Set.indicator_apply, Set.mem_Ioc]
  simp_rw [comp_stepProfile_eq_sum w n φ hφ]
  rw [integral_finsetSum]
  · simp_rw [hfun]
    simp_rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul,
      section3_cell_real_measure]
    rw [← Finset.mul_sum]
    ring
  · intro i _
    rw [hfun]
    exact (integrable_const (μ := profileMeasure) (φ ((w n).rate i))).indicator
      measurableSet_Ioc

/-- The finite rate mean equals the transform of the actual step profile. -/
theorem meanRemaining_eq_profileD (w : WeightArray) (n : ℕ) (t : ℝ) :
    meanRemaining (w n) t = profileD profileMeasure (stepProfile w n) t := by
  exact (integral_comp_stepProfile w n (rateKernel t) (by simp [rateKernel])).symm

/-- The finite arrival mean equals the actual profile transform, also on
the empty row: both sides are zero there. -/
theorem meanArrival_eq_profileF (w : WeightArray) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    meanArrival (w n) t = profileF profileMeasure (stepProfile w n) t := by
  haveI : IsProbabilityMeasure profileMeasure := by
    constructor
    simp [profileMeasure, Measure.restrict_apply, Real.volume_Ioo]
  have hmeas : Measurable (stepProfile w n) := by
    unfold stepProfile
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.ite measurableSet_Ioc measurable_const
  have hnonneg : ∀ x, 0 ≤ stepProfile w n x := by
    intro x
    unfold stepProfile
    exact Finset.sum_nonneg fun i _ => by
      split_ifs
      · exact (w n).positive i |>.le
      · exact le_rfl
  have hInt := integrable_survivalKernel (μ := profileMeasure)
    hmeas.aestronglyMeasurable (Eventually.of_forall hnonneg) ht
  have heq := integral_comp_stepProfile w n (fun a => 1 - survivalKernel t a)
    (by simp [survivalKernel])
  rw [integral_sub (integrable_const 1) hInt] at heq
  simpa [meanArrival, profileF, profileH] using heq.symm

end Luce
