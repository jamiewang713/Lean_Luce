import Luce.Section65GaussianVector
import Luce.Section65CharacteristicPerturbation

noncomputable section
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators
namespace Luce.Section6

theorem standardNormalVector_characteristic65 {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    (∫ z, Complex.exp ((linearCombination65 t z : ℂ)*I) ∂standardNormalVector ι) =
      Complex.exp (-((∑ i, (t i)^2 : ℝ) : ℂ)/2) := by
  have he (z : ι → ℝ) : Complex.exp ((linearCombination65 t z : ℂ)*I) =
      ∏ i : ι, Complex.exp (((t i*z i : ℝ) : ℂ)*I) := by
    simp only [linearCombination65,Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  simp_rw [he]
  unfold standardNormalVector
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Complex.exp (((t i*x : ℝ) : ℂ)*I))]
  have hi (i : ι) : (∫ x : ℝ, Complex.exp (((t i*x : ℝ) : ℂ)*I) ∂gaussianReal 0 1) =
      Complex.exp (-((t i : ℂ)^2)/2) := by
    have h := charFun_gaussianReal (μ := 0) (v := 1) (t i)
    simpa only [charFun_apply_real,Complex.ofReal_mul,Complex.ofReal_zero,NNReal.coe_one,
      Complex.ofReal_one,mul_zero,zero_mul,zero_sub,one_mul,neg_div] using h
  simp_rw [hi]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum,Complex.ofReal_pow]
  rw [← Finset.sum_div,Finset.sum_neg_distrib]

theorem linearCombination_blocks65 {ι J : Type*} [Fintype ι] [Fintype J]
    (a : ι → J → ℝ) (t : J → ℝ) (z : (ι × J) → ℝ) :
    linearCombination65 t (fun j => ∑ i, a i j*z (i,j)) =
      linearCombination65 (fun p : ι × J => t p.2*a p.1 p.2) z := by
  simp only [linearCombination65,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

theorem gaussian_blocks_characteristic65 {ι J : Type*} [Fintype ι] [Fintype J]
    (a : ι → J → ℝ) (ha : ∀ j, ∑ i, (a i j)^2 = 1) (t : J → ℝ) :
    (∫ z, Complex.exp ((linearCombination65 (fun p : ι × J => t p.2*a p.1 p.2) z : ℂ)*I)
      ∂standardNormalVector (ι × J)) =
      ∫ z, Complex.exp ((linearCombination65 t z : ℂ)*I) ∂standardNormalVector J := by
  have he : (∑ p : ι × J, (t p.2*a p.1 p.2)^2) = ∑ j, (t j)^2 := by
    simp only [Fintype.sum_prod_type,mul_pow]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum,ha j,mul_one]
  rw [standardNormalVector_characteristic65,standardNormalVector_characteristic65,he]

end Luce.Section6
