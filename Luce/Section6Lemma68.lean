import Luce.Section6IdealSpatialEstimate

noncomputable section
open Filter
namespace Luce.Section6

/-- The spatial assertion holds with K = 1 and kappa = 1. -/
theorem lemma68_spatial : Lemma68Contract.spatial := by
  intro f left right hp side hactive k a b ha hab hb
  let behavior := cornerBehavior left right side
  obtain ⟨hg,hq⟩ := hp.local_corner_parameters_pos side hactive
  obtain ⟨E,D,c,d,hE,hD,hc,htrace⟩ := idealTrace_refined68 side behavior hactive hg hq k
  obtain ⟨N,hN⟩ := eventually_atTop.mp (idealSpatialWindow68_eventually ha hab hb hc)
  let C := 2*(E+D)+2*|cornerCoefficient side behavior k|+1
  refine ⟨C,1,by dsimp [C]; positivity,by norm_num,1,max 1 N,le_max_left _ _,?_⟩
  intro n hn
  have hw := hN n ((le_max_right 1 N).trans hn)
  have h := idealSpatialTrace68_window_bound side behavior k hE.le hD.le hc.le htrace hw
  have hA : (0 : ℝ) < idealCoreLower n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (idealCoreLower_pos68 n))
  have hnlog := Real.log_natCast_nonneg n
  have hf : 0 ≤ (1+Real.log (n : ℝ))/(idealCoreLower n : ℝ) := by positivity
  simp only [pow_one, Real.rpow_neg_one]
  change |idealSpatialTrace side behavior k n a b-
    cornerCoefficient side behavior k*(b-a)*Real.log (n : ℝ)| ≤ _
  dsimp [C]
  rw [← div_eq_mul_inv, mul_div_assoc]
  nlinarith only [h, hf]

/-- Both assertions of manuscript Lemma 6.8, from the original profile hypotheses. -/
theorem lemma68 : Lemma68Contract.lemma68 := ⟨lemma68_total, lemma68_spatial⟩

end Luce.Section6
