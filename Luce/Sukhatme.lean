import Luce.SukhatmeContract
import Luce.SukhatmeConstants
import Luce.SukhatmeProfile
import Luce.Section65PowerContract
import Luce.Section65SpatialContract

/-! Corollary 1.9 of `fixed_points_sampled_profile.tex`: joint and spatial
Sukhatme cycle CLTs, mean asymptotics, localization, and the exact constants.
The probability spaces may vary with n. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
universe u
namespace Luce.Sukhatme
open Section6

/-- The unique active corner is the right corner. -/
def spatialEquiv (L J : ℕ) :
    SpatialIndex (.finite 1) (.power 1 1 1) L J ≃ (Fin L × Fin J) where
  toFun z := z.2
  invFun z := (⟨.right, trivial⟩, z)
  left_inv := by
    rintro ⟨⟨side, hside⟩, z⟩
    cases side
    · exact hside.elim
    · rfl
  right_inv _ := rfl

@[simp] theorem spatialEquiv_symm_apply (L J : ℕ) (z : Fin L × Fin J) :
    (spatialEquiv L J).symm z = (⟨.right, trivial⟩, z) := rfl

theorem normalizedCycleVector_eq {n : ℕ} (π : Equiv.Perm (Fin n)) (L : ℕ) :
    Section6.normalizedCycleVector π (.finite 1) (.power 1 1 1) L =
      Sukhatme.normalizedCycleVector π L := by
  funext k
  simp only [Section6.normalizedCycleVector, Sukhatme.normalizedCycleVector, totalCoefficient_eq]

theorem normalizedSpatialVector_eq {n : ℕ} (π : Equiv.Perm (Fin n))
    (L J : ℕ) (a b : Fin J → ℝ) :
    (fun z => Section6.normalizedSpatialVector π (.finite 1) (.power 1 1 1) L J a b
      ((spatialEquiv L J).symm z)) = Sukhatme.normalizedSpatialVector π L J a b := by
  funext z
  simp only [Section6.normalizedSpatialVector, Sukhatme.normalizedSpatialVector,
    spatialEquiv_symm_apply, cornerBehavior, rightCoefficient_eq]

theorem gaussian_spatial_reindex (L J : ℕ) (F : ((Fin L × Fin J) → ℝ) →ᵇ ℝ) :
    (∫ z, F (fun j => z ((spatialEquiv L J).symm j))
      ∂standardNormalVector (SpatialIndex (.finite 1) (.power 1 1 1) L J)) =
      ∫ z, F z ∂standardNormalVector (Fin L × Fin J) := by
  exact (measurePreserving_piCongrLeft
    (fun _ : Fin L × Fin J => ProbabilityTheory.gaussianReal 0 1)
    (spatialEquiv L J)).integral_comp' F

/-- Corollary 1.9, with all exact assertions in the independent closed contract. -/
theorem corollary19 : Corollary19.{u} := by
  refine ⟨coefficient_zero, coefficient_one, ?_⟩
  intro Ω mΩ P hP
  let : ∀ n, MeasurableSpace (Ω n) := mΩ
  let : ∀ n, IsProbabilityMeasure (P n) := hP
  intro π hπ hmass
  have hs : ∀ n (σ : Equiv.Perm (Fin n)),
      (P n).real {ω | π n ω = σ} = (sampled n).mass σ := by
    intro n σ
    rw [sampled_mass, hmass]
  have hp := powerLaw65 .interior Ω mΩ P hP sampled (fun x : ℝ => 1-x)
    (.finite 1) (.power 1 1 1) sampled_rates profile π hπ hs
  have hv : ∀ L : ℕ, ∀ F : (Fin L → ℝ) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (Sukhatme.normalizedCycleVector (π n ω) L) ∂P n)
        atTop (𝓝 (∫ z, F z ∂standardNormalVector (Fin L))) := by
    intro L F
    simpa only [normalizedCycleVector_eq] using hp.2 L F
  refine ⟨?_, hv, ?_, ?_⟩
  · intro k
    simpa only [totalCoefficient_eq] using hp.1 k
  · intro F
    let G : (Fin 1 → ℝ) →ᵇ ℝ := F.compContinuous ⟨fun z => z 0, continuous_apply 0⟩
    have hh := hv 1 G
    have he : (∫ z : Fin 1 → ℝ, F (z 0) ∂standardNormalVector (Fin 1)) =
        ∫ z, F z ∂ProbabilityTheory.gaussianReal 0 1 := by
      exact (measurePreserving_piUnique
        (fun _ : Fin 1 => ProbabilityTheory.gaussianReal 0 1)).integral_comp' F
    simpa only [G, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk, Sukhatme.normalizedCycleVector, Fin.val_zero,
      coefficient_zero, he] using hh
  · intro L J a b hab hd
    have hsp := spatial65 .interior Ω mΩ P hP sampled (fun x : ℝ => 1-x)
      (.finite 1) (.power 1 1 1) sampled_rates profile π hπ hs L J a b hab hd
    refine ⟨?_, ?_, ?_⟩
    · intro k j
      simpa only [spatialEquiv_symm_apply, cornerBehavior, rightCoefficient_eq]
        using (hsp.1 ((spatialEquiv L J).symm (k, j))).2
    · intro F
      let G : (SpatialIndex (.finite 1) (.power 1 1 1) L J → ℝ) →ᵇ ℝ :=
        F.compContinuous ⟨fun z j => z ((spatialEquiv L J).symm j),
          continuous_pi (fun j => continuous_apply _)⟩
      have hh := hsp.2.1 G
      simpa only [G, BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.coe_mk, normalizedSpatialVector_eq, gaussian_spatial_reindex] using hh
    · intro k j δ hδ
      exact hsp.2.2 ((spatialEquiv L J).symm (k, j)) δ hδ

end Luce.Sukhatme
