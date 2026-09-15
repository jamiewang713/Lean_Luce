import Luce.Section65RaceMomentCharacteristic
import Luce.Section65CenteringExpansion

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Luce.Section6

def affineCoeff65 (r : ℕ) (a b : ℝ) (j : Fin (r+1)) : ℝ :=
  (r.choose j.val : ℝ)*a^j.val*b^(r-j.val)

theorem affine_power65 (r : ℕ) (a b x : ℝ) :
    (a*x+b)^r = ∑ j : Fin (r+1), affineCoeff65 r a b j*x^j.val := by
  have h := centered_power_expansion65 (-b) (a*x) r
  simp only [sub_neg_eq_add,neg_neg,mul_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [affineCoeff65]
  ring

theorem affine_product_integral65 {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (X : Ω → ι → ℝ)
    (hX : ∀ r : ι → ℕ, Integrable (fun ω => ∏ i, X ω i^(r i)) P)
    (r : ι → ℕ) (a b : ι → ℝ) :
    (∫ ω, ∏ i, (a i*X ω i+b i)^(r i) ∂P) =
      ∑ v : (i : ι) → Fin (r i+1), (∏ i, affineCoeff65 (r i) (a i) (b i) (v i))*
        ∫ ω, ∏ i, X ω i^(v i).val ∂P := by
  simp_rw [affine_power65,Fintype.prod_sum,Finset.prod_mul_distrib]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro v hv
    exact (hX (fun i => (v i).val)).const_mul _

theorem race_affine_moments65 {ι : Type*} [Fintype ι]
    (w : WeightArray) (X : ∀ n, Equiv.Perm (Fin n) → ι → ℝ)
    (hX : ∀ r : ι → ℕ, Tendsto (fun n => ∫ clocks, ∏ i, X n (raceRankPermutation clocks) i^(r i)
      ∂exponentialRace (w n)) atTop (𝓝 (∏ i, gaussianMoment65 1 (r i))))
    (a b : ℕ → ι → ℝ)
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 1))
    (hb : ∀ i, Tendsto (fun n => b n i) atTop (𝓝 0)) (r : ι → ℕ) :
    Tendsto (fun n => ∫ clocks, ∏ i,
      (a n i*X n (raceRankPermutation clocks) i+b n i)^(r i) ∂exponentialRace (w n)) atTop
      (𝓝 (∏ i, gaussianMoment65 1 (r i))) := by
  classical
  have he (n : ℕ) := affine_product_integral65 (exponentialRace (w n))
    (fun clocks => X n (raceRankPermutation clocks))
    (fun s => integrable_race_permutation_statistic (w n) (fun R => ∏ i, X n R i^(s i))) r (a n) (b n)
  have ht := affine_product_integral65 (standardNormalVector ι) (fun z : ι → ℝ => z)
    standardNormalVector_mixed_integrable65 r (fun _ => 1) (fun _ => 0)
  simp only [one_mul,add_zero,standardNormalVector_mixed_moment65] at ht
  simp only [he]
  rw [ht]
  apply tendsto_finsetSum
  intro v hv
  apply Tendsto.mul _ (hX (fun i => (v i).val))
  apply tendsto_finsetProd
  intro i hi
  exact (((ha i).pow (v i).val).const_mul _).mul ((hb i).pow (r i-(v i).val))

end Luce.Section6
