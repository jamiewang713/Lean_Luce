import Luce.Section5BlockProductMeasure
import Luce.Section5ContractDefinitions

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce

/-- The manuscript's truncated intensity, on the literal closed cube. -/
def bulkCycleTraceIntensity (f : ℝ → ℝ) (α : ℝ) (k : ℕ) : ℝ :=
  (∫ x in cyclicBulkCube (k+1) α, cycleTraceIntegrand f k x) / (k+1 : ℝ)

theorem block_density_integral_factorization (f : ℝ → ℝ) (L : ℕ)
    (m : Fin L → ℕ) (μ : Measure ℝ) [SigmaFinite μ] :
    (∫ x, ∏ a : Section5.CycleVertex L m,
      cyclicProfileDensity f (x a) (x (Section5.cycleBlockPermutation L m a))
      ∂Measure.pi (fun _ => μ)) =
      ∏ ell : Fin L, (∫ x, cycleTraceIntegrand f ell.val x
        ∂Measure.pi (fun _ : Fin (ell.val+1) => μ)) ^ m ell := by
  classical
  have hp (x : Section5.CycleVertex L m → ℝ) :
      (∏ a, cyclicProfileDensity f (x a) (x (Section5.cycleBlockPermutation L m a))) =
      ∏ b : Section5.CycleSlot L m, cycleTraceIntegrand f b.1.val (fun j => x ⟨b,j⟩) := by
    exact Fintype.prod_sigma (fun a : Section5.CycleVertex L m =>
      cyclicProfileDensity f (x a) (x (Section5.cycleBlockPermutation L m a)))
  simp_rw [hp]
  rw [integral_block_product (fun (b : Section5.CycleSlot L m) (_ : Fin (b.1.val+1)) => μ)]
  simp only [Section5.CycleSlot, Fintype.prod_sigma, cycleTraceIntegrand]
  apply Finset.prod_congr rfl
  intro ell _
  change (∏ _ : Fin (m ell), (∫ x, cycleTraceIntegrand f ell.val x
    ∂Measure.pi (fun _ : Fin (ell.val+1) => μ))) = _
  simp [cycleTraceIntegrand]

/-- Reindexing by a finite equivalence preserves the literal cyclic integral. -/
theorem cyclic_integral_reindex {V : Type*} [Fintype V] {r : ℕ}
    (e : V ≃ Fin r) (τ : Equiv.Perm V) (f : ℝ → ℝ)
    (μ : Measure ℝ) [SigmaFinite μ] :
    (∫ x, ∏ a, cyclicProfileDensity f (x a) (x ((e.symm.trans (τ.trans e)) a))
      ∂Measure.pi (fun _ : Fin r => μ)) =
      ∫ x, ∏ a, cyclicProfileDensity f (x a) (x (τ a))
        ∂Measure.pi (fun _ : V => μ) := by
  classical
  rw [← (measurePreserving_piCongrLeft (fun _ : Fin r => μ) e).integral_comp']
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
    Equiv.trans_apply, Equiv.symm_apply_apply]
  simpa only [Equiv.piCongrLeft_apply, eq_rec_constant] using
    e.symm.prod_comp (fun a => cyclicProfileDensity f (x a) (x (τ a)))

/-- The full block integral with its original rotation divisor factors
into the individual manuscript intensities. This identity is unconditional
in the density; the separate local-limit proof supplies its analytic use. -/
theorem canonical_block_integral_eq_intensity_product (f : ℝ → ℝ)
    (L : ℕ) (m : Fin L → ℕ) (α : ℝ) :
    ((∫ x in cyclicBulkCube (Fintype.card (Section5.CycleVertex L m)) α,
      ∏ a, cyclicProfileDensity f (x a) (x (factorialBlockPermutation L m a))) /
        ∏ ell : Fin L, ((ell.val+1 : ℕ) : ℝ)^m ell) =
      ∏ ell : Fin L, bulkCycleTraceIntensity f α ell.val ^ m ell := by
  classical
  have hcube (r : ℕ) : (volume : Measure (Fin r → ℝ)).restrict (cyclicBulkCube r α) =
      Measure.pi (fun _ : Fin r => (volume : Measure ℝ).restrict (Icc 0 α)) := by
    exact Measure.restrict_pi_pi (fun _ : Fin r => (volume : Measure ℝ)) (fun _ => Icc 0 α)
  simp only [hcube, factorialBlockPermutation]
  rw [cyclic_integral_reindex, block_density_integral_factorization]
  simp only [bulkCycleTraceIntensity, hcube, div_pow, Finset.prod_div_distrib,
    Nat.cast_add, Nat.cast_one]

end Luce
