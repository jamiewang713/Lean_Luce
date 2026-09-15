import Luce.Section1SukhatmeDefinitions
import Luce.Section6Sampling

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Luce.Sukhatme
open Section6

theorem profile : PowerProfile (fun x : ℝ => 1-x) (.finite 1) (.power 1 1 1) := by
  refine ⟨(continuous_const.sub continuous_id).continuousOn,
    (fun x hx => sub_pos.mpr hx.2), ?_, ?_, Or.inr trivial⟩
  · exact ⟨by norm_num, by
      simpa using (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun x : ℝ => 1-x) (𝓝[>] 0) (𝓝 (1-0)))⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    apply Asymptotics.IsBigO.of_bound (0 : ℝ)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := (show 0 < s from hs).ne'
    simp [Real.rpow_one, hs0]

/-- Interior-grid rates for f(x)=1-x, obtained by positive row scaling. -/
def sampled : WeightArray := fun n =>
  (weights n).scale (((n : ℝ) + 1)⁻¹) (by positivity)

theorem sampled_rates : SampledRates .interior sampled (fun x : ℝ => 1-x) := by
  intro n i
  change ((n : ℝ) + 1)⁻¹ * ((n : ℝ) - i.val) =
    1 - (((i.val : ℝ) + 1) / ((n : ℝ) + 1))
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem sampled_mass (n : ℕ) (π : Equiv.Perm (Fin n)) :
    (sampled n).mass π = (weights n).mass π :=
  (weights n).mass_scale _ _ π

end Luce.Sukhatme
