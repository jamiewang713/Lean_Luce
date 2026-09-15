import Luce.Section6OutsideLeftWeightedSubset
import Luce.Section6LeftOutsideTarget

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- The actual moderate left-target contribution for sources outside the
left source block, with weight (n/h)^kappa (larger than the manuscript
weight when kappa is nonnegative). The rate upper
bound and all analytic estimates are derived from the sampled profile. -/
theorem PowerProfile.outside_left_weighted_insertion_row {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    {sigma kappa : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hk : kappa < alpha) (p0 : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ sigma ∧ delta ≤ 1/2 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 0 < n →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ),
    sigma ≤ ((i.val : ℝ)+1)/(n : ℝ) → 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, 8*r+8 ≤ j.val+1 ∧ ((j.val : ℝ)+1)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal (((n : ℝ)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, d, delta, hB, hd, hdelta, hds, hb⟩ :=
    hp.left_outside_shifted_insertion_Lp hsigma hsigma1 p0
  obtain ⟨R, hR, hrate⟩ := hp.sampled_upper_outside_left hsigma hsigma1
  let K : ℝ := 1/(alpha-kappa)+2*(1/2 : ℝ)^(alpha-kappa)
  have hK : 0 < K := by dsimp [K]; have ht := sub_pos.mpr hk; positivity
  refine ⟨B*(R*K), min delta (1/2), by positivity, lt_min hdelta (by norm_num),
    (min_le_left _ _).trans hds, min_le_right _ _, ?_⟩
  intro grid w hw n r hn i s removed q p hi hpp hpp0 hs
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hir := (w n).positive i
  let g : Fin n → ℝ := fun j => ((n : ℝ)/((j.val : ℝ)+1))^kappa*
    ((w n).rate i*(((j.val : ℝ)+1)/(n : ℝ))^alpha/((j.val : ℝ)+1))*
    Real.exp (-d*((w n).rate i*(((j.val : ℝ)+1)/(n : ℝ))^alpha))
  have hg (j : Fin n) : 0 ≤ g j := by dsimp [g]; positivity
  have hhalf : ∀ j ∈ s, 2*(j.val+1) ≤ n := by
    intro j hj
    have hjh := ((hs j hj).2.1).trans (min_le_right _ _)
    have hjh' := (div_le_iff₀ hnR).mp hjh
    have hreal : 2*((j.val : ℝ)+1) ≤ n := by linarith
    exact_mod_cast hreal
  have hsum : (∑ j ∈ s, g j) ≤ (w n).rate i*K :=
    outside_left_weighted_subset_bound hn hir.le hk hd.le s hhalf
  calc
    _ ≤ ∑ j ∈ s, ENNReal.ofReal (B*g j) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hjrange, hjsmall, hjremoved, hjshift⟩ := hs j hj
      have hsmall : ((j.val+1 : ℕ) : ℝ)/(n : ℝ) ≤ delta := by
        simpa only [Nat.cast_add, Nat.cast_one] using hjsmall.trans (min_le_left _ _)
      have hcard : (Finset.univ \ removed j).card = n-(removed j).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have hq : q j < (Finset.univ \ removed j).card := by
        rw [hcard]
        exact shifted_left_nonterminal hjremoved hjrange (hhalf j hj) (by simpa using hjshift)
      have he := hb grid w hw n r (j.val+1) hn hjrange hsmall
        (removed j) hjremoved i ⟨q j, hq⟩ p (by simpa using hjshift) hi hpp hpp0
      have hm := mul_le_mul_of_nonneg_left he
        (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (((n : ℝ)/((j.val : ℝ)+1))^kappa) from zero_le)
      have hwgt : 0 ≤ ((n : ℝ)/((j.val : ℝ)+1))^kappa := by positivity
      rw [← ENNReal.ofReal_mul hwgt] at hm
      convert hm using 1 <;> simp only [g, Nat.cast_add, Nat.cast_one] <;> congr 1 <;> ring
    _ = ENNReal.ofReal (B*(∑ j ∈ s, g j)) := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg hB.le (hg j))]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (hsum.trans (mul_le_mul_of_nonneg_right (hrate grid w hw n i hi) hK.le)) hB.le

/-- The manuscript's exact left weight, for outside sources and moderate
left targets. Boundary targets are a separate remaining contribution. -/
theorem PowerProfile.outside_left_manuscript_weighted_row {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    {sigma kappa : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hk0 : 0 ≤ kappa) (hk : kappa < alpha) (p0 : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ sigma ∧ delta ≤ 1/2 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 0 < n →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ),
    sigma ≤ ((i.val : ℝ)+1)/(n : ℝ) → 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, 8*r+8 ≤ j.val+1 ∧ ((j.val : ℝ)+1)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨C, delta, hC, hd, hds, hdh, hb⟩ :=
    hp.outside_left_weighted_insertion_row hsigma hsigma1 hk p0
  refine ⟨C, delta, hC, hd, hds, hdh, ?_⟩
  intro grid w hw n r hn i s removed q p hi hpp hpp0 hs
  apply le_trans _ (hb grid w hw n r hn i s removed q p hi hpp hpp0 hs)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow (by positivity) _ hk0
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show i.val+1 ≤ n by omega)

end Luce.Section6
