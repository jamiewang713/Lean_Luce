import Luce.Section65CoreTargetMoments
import Luce.Section65IdealMean
import Luce.Section65CoefficientPositivity
import Luce.Section65LogWindows

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace Luce.Section6

def spatialCategory65 {left right : EndpointBehavior} {L J : ℕ} (a b : Fin J → ℝ)
    (z : SpatialIndex left right L J) : CoreCycleCategory :=
  ⟨z.1.val,z.2.1.val,.interval (fun n => (n : ℝ)^(a z.2.2)) (fun n => (n : ℝ)^(b z.2.2))⟩

def spatialCoefficient65 {left right : EndpointBehavior} {L J : ℕ} (a b : Fin J → ℝ)
    (z : SpatialIndex left right L J) : ℝ :=
  cornerCoefficient z.1.val (cornerBehavior left right z.1.val) z.2.1.val*(b z.2.2-a z.2.2)

theorem spatialCategories_disjoint65 {left right : EndpointBehavior} {L J : ℕ}
    (a b : Fin J → ℝ)
    (hd : Pairwise fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) :
    FiniteCategoriesDisjoint65 (spatialCategory65 (left := left) (right := right) (L := L) a b) := by
  intro n hn i j hij hs hk m hm
  have hijj : i.2.2 ≠ j.2.2 := by
    intro he
    apply hij
    exact Prod.ext (Subtype.ext hs) (Prod.ext (Fin.ext hk) he)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  change ((n : ℝ)^(a i.2.2) < (m : ℝ) ∧ (m : ℝ) ≤ (n : ℝ)^(b i.2.2)) ∧
    ((n : ℝ)^(a j.2.2) < (m : ℝ) ∧ (m : ℝ) ≤ (n : ℝ)^(b j.2.2)) at hm
  have hm0 : (0 : ℝ) < m := (Real.rpow_pos_of_pos hn0 _).trans hm.1.1
  have hmem {q : Fin J} (hq : (n : ℝ)^(a q) < (m : ℝ) ∧ (m : ℝ) ≤ (n : ℝ)^(b q)) :
      Real.log (m : ℝ)/Real.log (n : ℝ) ∈ Ioc (a q) (b q) := by
    rw [mem_Ioc,lt_div_iff₀ hl,div_le_iff₀ hl]
    rw [← Real.log_rpow hn0,← Real.log_rpow hn0]
    exact ⟨Real.log_lt_log (Real.rpow_pos_of_pos hn0 _) hq.1,Real.log_le_log hm0 hq.2⟩
  exact Set.disjoint_left.mp (hd hijj) (hmem hm.1) (hmem hm.2)

theorem spatial_core_target_moments65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (L J : ℕ) (a b : Fin J → ℝ)
    (hab : ∀ j, 0 < a j ∧ a j < b j ∧ b j < 1)
    (hd : Pairwise fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))
    (r : SpatialIndex left right L J → ℕ) :
    Tendsto (fun n => ∫ clocks, ∏ z : SpatialIndex left right L J,
      (((coreCategoryCount (raceRankPermutation clocks) (spatialCategory65 a b z) : ℝ)-
        spatialCoefficient65 a b z*Real.log (n : ℝ))/
        Real.sqrt (spatialCoefficient65 a b z*Real.log (n : ℝ)))^(r z) ∂exponentialRace (w n))
      atTop (𝓝 (∏ z, gaussianMoment65 1 (r z))) := by
  apply core_target_mixed_moments65 f left right hp grid w hs
    (spatialCategory65 a b) (fun z => z.1.property) (spatialCategories_disjoint65 a b hd)
    (spatialCoefficient65 a b)
  · intro z
    exact mul_pos (hp.cornerCoefficient_pos65 _ z.1.property _) (sub_pos.mpr (hab z.2.2).2.1)
  · intro z
    exact idealSpatialTrace_meanApprox65 f left right hp _ z.1.property _
      (hab z.2.2).1 (hab z.2.2).2.1 (hab z.2.2).2.2

end Luce.Section6
