import Luce.Section6DensityEnvelope
import Luce.Section6Lemma66Contract

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Complete closed statement of manuscript Lemma 6.6, proved by replacing
one clock at a time. The universal constant is explicitly `3^ell`. -/
theorem lemma66 : Lemma66Contract.lemma66 := by
  intro ell hell
  refine ⟨(3 : ℝ)^ell, pow_pos (by norm_num) _, ?_⟩
  intro Ω _ P _ n E g hLaw hIndependent S h hh0 hh hdom
  exact integrable_density_envelope P E g hLaw hIndependent S ell hell h
    (Filter.Eventually.of_forall hh0) hh
    (fun i hi => Filter.Eventually.of_forall (hdom i hi))

end Luce.Section6
