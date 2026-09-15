import Luce.Section7Definitions
import Luce.Profile

/-! # The candidate bulk density in Section 7

These are population definitions and their normalization. They do not
assert a microscopic local law, which Section 7 explicitly leaves as a
model-specific input.
-/

open MeasureTheory Set

namespace Luce.Section7
noncomputable section

/-- `F(t) = ∫₀¹ G(x,t) dx`. -/
def populationCDF (G : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioc (0 : ℝ) 1, G x t

/-- `d(t) = ∫₀¹ g(x,t) dx`. -/
def populationDensity (g : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioc (0 : ℝ) 1, g x t

/-- A population inverse, used only for values in the range of `F`. -/
def populationQuantile (G : ℝ → ℝ → ℝ) (y : ℝ) : ℝ :=
  Function.invFun (populationCDF G) y

theorem populationCDF_quantile (G : ℝ → ℝ → ℝ) {y : ℝ}
    (hy : y ∈ Set.range (populationCDF G)) :
    populationCDF G (populationQuantile G y) = y := by
  obtain ⟨t, rfl⟩ := hy
  exact Function.apply_invFun_apply

theorem populationQuantile_unique (G : ℝ → ℝ → ℝ)
    (hF : StrictMono (populationCDF G)) {y t : ℝ} (ht : populationCDF G t = y) :
    populationQuantile G y = t := by
  apply hF.injective
  exact (populationCDF_quantile G ⟨t, ht⟩).trans ht.symm

/-- Equation `eq:general-clock-density`, at any specified inverse time. -/
def bulkDensityAt (g : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  g x t / populationDensity g t

/-- Equation `eq:general-clock-density` with `t_y = F⁻¹(y)`. -/
def bulkDensity (G g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  bulkDensityAt g x (populationQuantile G y)

theorem bulkDensityAt_nonneg (g : ℝ → ℝ → ℝ) (x t : ℝ)
    (hg : 0 ≤ g x t) (hd : 0 < populationDensity g t) :
    0 ≤ bulkDensityAt g x t := div_nonneg hg hd.le

theorem bulkDensityAt_integrable (g : ℝ → ℝ → ℝ) (t : ℝ)
    (hg : IntegrableOn (fun x => g x t) (Ioc (0 : ℝ) 1)) :
    IntegrableOn (fun x => bulkDensityAt g x t) (Ioc (0 : ℝ) 1) :=
  hg.div_const _

/-- Each column of the candidate density has integral one. -/
theorem bulkDensityAt_integral (g : ℝ → ℝ → ℝ) (t : ℝ)
    (hd : populationDensity g t ≠ 0) :
    (∫ x in Ioc (0 : ℝ) 1, bulkDensityAt g x t) = 1 := by
  simp only [bulkDensityAt, integral_div]
  exact div_self hd

theorem bulkDensity_integral (G g : ℝ → ℝ → ℝ) (y : ℝ)
    (hd : 0 < populationDensity g (populationQuantile G y)) :
    (∫ x in Ioc (0 : ℝ) 1, bulkDensity G g x y) = 1 :=
  bulkDensityAt_integral g _ hd.ne'

/-- The exponential density yields the rate-kernel ratio used earlier. -/
theorem bulkDensityAt_exponential (f : ℝ → ℝ) (x t : ℝ) :
    bulkDensityAt (fun x t => f x * Real.exp (-t * f x)) x t =
      rateKernel t (f x) / profileD (volume.restrict (Ioc (0 : ℝ) 1)) f t := rfl

end
end Luce.Section7
