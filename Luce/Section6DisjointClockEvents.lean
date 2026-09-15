import Luce.Section6GapOrderPartition

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Independence of measurable events depending on disjoint clock blocks.
Coordinate support is an explicit helper premise, discharged for gap events. -/
theorem exponentialRace_inter_of_disjoint_support {n : ℕ} (w : Weights n)
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (A B : Set (Fin n → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hSA : ∀ x y, (∀ i ∈ S, x i = y i) → (x ∈ A ↔ y ∈ A))
    (hTB : ∀ x y, (∀ i ∈ T, x i = y i) → (x ∈ B ↔ y ∈ B)) :
    exponentialRace w (A ∩ B) = exponentialRace w A * exponentialRace w B := by
  classical
  let extend (U : Finset (Fin n)) (z : U → ℝ) (i : Fin n) : ℝ :=
    if hi : i ∈ U then z ⟨i, hi⟩ else 0
  have hm (U : Finset (Fin n)) : Measurable (extend U) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ U
    · simpa only [extend, dif_pos hi] using (measurable_pi_apply (⟨i, hi⟩ : U))
    · simp only [extend, dif_neg hi]
      exact measurable_const
  have hpreA : (fun x : Fin n → ℝ => fun i : S => x i) ⁻¹' ((extend S) ⁻¹' A) = A := by
    ext x
    apply hSA
    intro i hi
    simp [extend, hi]
  have hpreB : (fun x : Fin n → ℝ => fun i : T => x i) ⁻¹' ((extend T) ⁻¹' B) = B := by
    ext x
    apply hTB
    intro i hi
    simp [extend, hi]
  have hind := iIndepFun.indepFun_finset S T hST (exponentialRace_independent w)
    (fun i => measurable_pi_apply i)
  have hh := hind.measure_inter_preimage_eq_mul ((extend S) ⁻¹' A) ((extend T) ⁻¹' B)
    (hA.preimage (hm S)) (hB.preimage (hm T))
  simpa only [hpreA, hpreB] using hh

/-- Finite product factorization for disjoint coordinate blocks, derived
from the actual independent exponential law. -/
theorem exponentialRace_biInter_disjoint_support {ι : Type*} {n : ℕ} (w : Weights n)
    (block : ι → Finset (Fin n)) (A : ι → Set (Fin n → ℝ))
    (hA : ∀ i, MeasurableSet (A i))
    (hsupport : ∀ i x y, (∀ l ∈ block i, x l = y l) → (x ∈ A i ↔ y ∈ A i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (block i) (block j)) (s : Finset ι) :
    exponentialRace w {x | ∀ i ∈ s, x ∈ A i} = ∏ i ∈ s, exponentialRace w (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    let B := {x : Fin n → ℝ | ∀ i ∈ s, x ∈ A i}
    have hB : MeasurableSet B := by
      dsimp only [B]
      simp only [Set.ofPred_forall]
      exact MeasurableSet.biInter s.countable_toSet (fun i _ => hA i)
    have hdis : Disjoint (block k) (s.biUnion block) := by
      apply Finset.disjoint_left.mpr
      intro l hl hls
      obtain ⟨j, hj, hlj⟩ := Finset.mem_biUnion.mp hls
      exact Finset.disjoint_left.mp (hdisjoint k j (by intro he; subst j; exact hk hj)) hl hlj
    have hdep : ∀ x y, (∀ l ∈ s.biUnion block, x l = y l) → (x ∈ B ↔ y ∈ B) := by
      intro x y he
      constructor
      · intro hx i hi
        exact (hsupport i x y (fun l hl => he l (Finset.mem_biUnion.mpr ⟨i, hi, hl⟩))).mp (hx i hi)
      · intro hy i hi
        exact (hsupport i x y (fun l hl => he l (Finset.mem_biUnion.mpr ⟨i, hi, hl⟩))).mpr (hy i hi)
    have hh := exponentialRace_inter_of_disjoint_support w (block k) (s.biUnion block)
      hdis (A k) B (hA k) hB (hsupport k) hdep
    have heq : {x : Fin n → ℝ | ∀ i ∈ insert k s, x ∈ A i} = A k ∩ B := by
      ext x
      simp [B]
    rw [heq, hh, Finset.prod_insert hk]
    exact congrArg (fun z => exponentialRace w (A k)*z) ih

end Luce.Section6
