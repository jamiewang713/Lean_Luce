import Luce.Section5FactorialLocal

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce

/-- Grouping finitely many independent coordinates into blocks preserves
their product measure. This is a representation theorem, not an independence
assumption on the Luce model. -/
theorem measurePreserving_block_uncurry {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (μ : (i : ι) → κ i → Measure ℝ)
    [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (_ : ι) (_ : κ _) => ℝ)).symm
      (Measure.pi (fun i => Measure.pi (μ i)))
      (Measure.pi (fun p : Sigma κ => μ p.1 p.2)) := by
  classical
  refine ⟨(MeasurableEquiv.piCurry _).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (MeasurableEquiv.piCurry _).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.piCurry (fun (_ : ι) (_ : κ _) => ℝ)).symm ⁻¹'
      (Set.pi Set.univ s) =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i,j⟩)) := by
    ext x
    simp [Set.mem_pi, MeasurableEquiv.coe_piCurry_symm, Sigma.uncurry, Sigma.forall]
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_sigma]

/-- Fubini for functions of disjoint original blocks, with no assumed
integrability or boundedness of the coordinate density. -/
theorem integral_block_product {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (μ : (i : ι) → κ i → Measure ℝ)
    [∀ i j, SigmaFinite (μ i j)] (F : (i : ι) → (κ i → ℝ) → ℝ) :
    (∫ x, ∏ i, F i (fun j => x ⟨i,j⟩)
      ∂Measure.pi (fun p : Sigma κ => μ p.1 p.2)) =
      ∏ i, ∫ x, F i x ∂Measure.pi (μ i) := by
  rw [← (measurePreserving_block_uncurry μ).integral_comp']
  exact integral_fintype_prod_eq_prod F

end Luce
