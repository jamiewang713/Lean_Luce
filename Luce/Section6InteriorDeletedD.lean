import Luce.Section6InteriorPopulationD
import Luce.Section6LargeTimePopulation

noncomputable section
namespace Luce.Section6

/-- Bounded deletions preserve compact-time weighted population bounds. -/
theorem interior_deletedD_bounds {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 1))
    (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x)
    {s T : ℝ} (hs : 0 < s) (hsT : s ≤ T) (r : ℕ) :
    ∃ a C N : ℝ, 0 < a ∧ 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, N ≤ (n : ℝ) → ∀ t : ℝ, s ≤ t → t ≤ T →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
      a ≤ deletedD (w n) removed 1 t ∧ deletedD (w n) removed 1 t ≤ C := by
  obtain ⟨a, C, ha, hC, hbounds⟩ := interior_populationD_bounds hf hpos hs hsT
  let U := Real.exp (-1)/s
  have hU : 0 < U := div_pos (Real.exp_pos _) hs
  refine ⟨a/2, C+a/2, max 8 (2*(r : ℝ)*U/a), by positivity, by positivity,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro grid w hw n hlarge t hst htT removed hremoved
  have hn8R : (8 : ℝ) ≤ n := (le_max_left _ _).trans hlarge
  have hn8 : 8 ≤ n := by exact_mod_cast hn8R
  have hnR : (0 : ℝ) < n := by linarith
  have ht : 0 < t := hs.trans_le hst
  have hbase := hbounds grid w hw n hn8 t hst htT
  have hdiff := populationD_one_deletion_bound (w n) removed hremoved ht
  have htime : Real.exp (-1)/t ≤ U :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le hs hst
  have herror : (r : ℝ)*(Real.exp (-1)/t)/(n : ℝ) ≤ a/2 := by
    have hcut : 2*(r : ℝ)*U/a ≤ (n : ℝ) := (le_max_right _ _).trans hlarge
    have hcut' := (div_le_iff₀ ha).mp hcut
    apply (div_le_iff₀ hnR).mpr
    have hh := mul_le_mul_of_nonneg_left htime (Nat.cast_nonneg r)
    nlinarith
  have habs := abs_le.mp (hdiff.trans herror)
  constructor <;> linarith [hbase.1, hbase.2, habs.1, habs.2]

/-- The interior weighted-population part of the quantile lemma, including
arbitrary bounded deletions. All compact-time premises are discharged. -/
theorem PowerProfile.interior_quantile_deletedD_bounds {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (he : 0 < eps) (r : ℕ) :
    ∃ a C N : ℝ, 0 < a ∧ 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ x : ℝ, eps ≤ x → x ≤ 1-eps →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
      (a ≤ deletedD (w n) removed 1 (arrivalQuantile (w n) x) ∧
        deletedD (w n) removed 1 (arrivalQuantile (w n) x) ≤ C) ∧
      (a ≤ deletedD (w n) removed 1 (survivorQuantile (w n) x) ∧
        deletedD (w n) removed 1 (survivorQuantile (w n) x) ≤ C) := by
  obtain ⟨s, T, Nt, hs, _, hNt, htimes⟩ := hp.interior_quantile_time_bounds he
  obtain ⟨a, C, Nd, ha, hC, hNd, hD⟩ := interior_deletedD_bounds hp.1 hp.2.1
    hs (show s ≤ max T s from le_max_right _ _) r
  refine ⟨a, C, max Nt Nd, ha, hC, hNt.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge x hx hx' removed hremoved
  have ht := htimes grid w hw n hn ((le_max_left _ _).trans hlarge) x hx hx'
  have hlargeD := (le_max_right _ _).trans hlarge
  exact ⟨hD grid w hw n hlargeD _ ht.1.1 (ht.1.2.trans (le_max_left _ _)) removed hremoved,
    hD grid w hw n hlargeD _ ht.2.1 (ht.2.2.trans (le_max_left _ _)) removed hremoved⟩

/-- In particular the original population satisfies n*D comparable to n
at both interior quantiles. -/
theorem PowerProfile.interior_quantile_populationD_bounds {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (he : 0 < eps) :
    ∃ a C N : ℝ, 0 < a ∧ 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ x : ℝ, eps ≤ x → x ≤ 1-eps →
      (a*(n : ℝ) ≤ (n : ℝ)*populationD (w n) 1 (arrivalQuantile (w n) x) ∧
        (n : ℝ)*populationD (w n) 1 (arrivalQuantile (w n) x) ≤ C*(n : ℝ)) ∧
      (a*(n : ℝ) ≤ (n : ℝ)*populationD (w n) 1 (survivorQuantile (w n) x) ∧
        (n : ℝ)*populationD (w n) 1 (survivorQuantile (w n) x) ≤ C*(n : ℝ)) := by
  obtain ⟨a, C, N, ha, hC, hN, hb⟩ := hp.interior_quantile_deletedD_bounds he 0
  refine ⟨a, C, N, ha, hC, hN, ?_⟩
  intro grid w hw n hn hlarge x hx hx'
  have hh := hb grid w hw n hn hlarge x hx hx' ∅ (by simp)
  simp only [deletedD, Finset.sdiff_empty] at hh
  change (a ≤ populationD (w n) 1 (arrivalQuantile (w n) x) ∧
    populationD (w n) 1 (arrivalQuantile (w n) x) ≤ C) ∧
    (a ≤ populationD (w n) 1 (survivorQuantile (w n) x) ∧
    populationD (w n) 1 (survivorQuantile (w n) x) ≤ C) at hh
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · constructor
    · simpa only [mul_comm a] using mul_le_mul_of_nonneg_left hh.1.1 hnR
    · simpa only [mul_comm C] using mul_le_mul_of_nonneg_left hh.1.2 hnR
  · constructor
    · simpa only [mul_comm a] using mul_le_mul_of_nonneg_left hh.2.1 hnR
    · simpa only [mul_comm C] using mul_le_mul_of_nonneg_left hh.2.2 hnR

end Luce.Section6
