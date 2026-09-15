import Luce.Section6Contract

/-! Closed statement of manuscript Lemma 6.12, `lem:sp-interior-grid`.
The three existing limit-theorem contracts retain their original profile
hypotheses and conclusions, with sampling at the one-based label i/(n+1).
This statement imports only definitions, independently of its proof. -/

universe u
namespace Luce.Section6.Lemma612Contract

def lemma612 : Prop :=
  SampledProfileContract.powerLaw.{u} .interior ∧
    SampledProfileContract.spatial.{u} .interior ∧
    SampledProfileContract.critical.{u} .interior

end Luce.Section6.Lemma612Contract
