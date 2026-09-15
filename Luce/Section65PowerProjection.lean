import Luce.Section65PowerCategories
import Luce.Section65GaussianProjection

noncomputable section
open scoped BigOperators
namespace Luce.Section6

def powerCornerWeight65 (left right : EndpointBehavior) (s : ActiveCorner65 left right) (k : ℕ) : ℝ :=
  Real.sqrt (cornerCoefficient s.val (cornerBehavior left right s.val) k/totalCoefficient left right k)

theorem powerCornerWeight_square_sum65 {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (k : ℕ) :
    (∑ s : ActiveCorner65 left right, (powerCornerWeight65 left right s k)^2) = 1 := by
  have hB := hp.totalCoefficient_pos65 k
  have he (s : ActiveCorner65 left right) : (powerCornerWeight65 left right s k)^2 =
      cornerCoefficient s.val (cornerBehavior left right s.val) k/totalCoefficient left right k :=
    Real.sq_sqrt (div_nonneg (hp.cornerCoefficient_pos65 _ s.property _).le hB.le)
  simp_rw [he]
  rw [← Finset.sum_div,sum_active_coefficients65,div_self hB.ne']

theorem weighted_normalization65 {c B l : ℝ} (hc : 0 < c) (hB : 0 < B) (hl : 0 < l) (x : ℝ) :
    Real.sqrt (c/B)*((x-c*l)/Real.sqrt (c*l)) = (x-c*l)/Real.sqrt (B*l) := by
  have hsc := (Real.sqrt_pos.mpr hc).ne'
  have hsB := (Real.sqrt_pos.mpr hB).ne'
  have hsl := (Real.sqrt_pos.mpr hl).ne'
  rw [Real.sqrt_div' _ hB.le,Real.sqrt_mul hc.le,Real.sqrt_mul hB.le]
  field_simp <;> ring

theorem totalCore_normalized_projection65 {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) {n : ℕ} (hl : 0 < Real.log (n : ℝ))
    (R : Equiv.Perm (Fin n)) (k : ℕ) :
    (totalCoreCount65 R left right k-totalCoefficient left right k*Real.log (n : ℝ))/
      Real.sqrt (totalCoefficient left right k*Real.log (n : ℝ)) =
      ∑ s : ActiveCorner65 left right, powerCornerWeight65 left right s k*
        (((coreCategoryCount R (cornerCoreCategory65 s.val k) : ℝ)-
          cornerCoefficient s.val (cornerBehavior left right s.val) k*Real.log (n : ℝ))/
          Real.sqrt (cornerCoefficient s.val (cornerBehavior left right s.val) k*Real.log (n : ℝ))) := by
  have he (s : ActiveCorner65 left right) := weighted_normalization65
    (hp.cornerCoefficient_pos65 _ s.property k) (hp.totalCoefficient_pos65 k) hl
    (coreCategoryCount R (cornerCoreCategory65 s.val k) : ℝ)
  simp only [powerCornerWeight65,he]
  rw [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.sum_mul,sum_active_coefficients65]
  rfl

end Luce.Section6
