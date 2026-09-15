import Luce.Section6RightRemainingRate

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Compact label intervals have uniformly bounded positive sampled rates.
Only continuity and positivity on the open interval are used. -/
theorem interior_sampled_rate_bounds {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 1))
    (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x)
    {eps : ℝ} (heps : 0 < eps) (heps' : eps < 1) :
    ∃ d M : ℝ, 0 < d ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ i : Fin n,
      eps ≤ ((i.val : ℝ)+1)/(n : ℝ) →
      eps ≤ ((i.rev.val : ℝ)+1)/(n : ℝ) →
      d ≤ (w n).rate i ∧ (w n).rate i ≤ M := by
  obtain ⟨d, M, hd, hM, hbound⟩ := positive_continuous_compact_bounds hf hpos
    (half_pos heps) (show 1-eps/2 < 1 by linarith)
    (show eps/2 ≤ 1-eps/2 by linarith)
  refine ⟨d, M, hd, hM, ?_⟩
  intro grid w hw n i hi hir
  rw [hw n i]
  apply hbound
  have hleft := samplePoint_ge_half_label grid i
  have hright := samplePoint_ge_half_label grid i.rev
  rw [samplePoint_rev] at hright
  constructor <;> linarith

/-- A positive macroscopic survivor population has a linear total rate.
Both allowed right endpoint behaviors are covered, without a shell input. -/
theorem PowerProfile.interior_remaining_rate {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ remaining : Finset (Fin n),
      eps*(n : ℝ) ≤ (remaining.card : ℝ) →
      C*(n : ℝ) ≤ ∑ i ∈ remaining, (w n).rate i := by
  classical
  cases right with
  | finite c =>
    obtain ⟨d, hd, hbound⟩ := hp.global_lower_of_right_finite
    refine ⟨eps*d, mul_pos heps hd, ?_⟩
    intro grid w hw n hn remaining hcard
    calc
      _ = (eps*(n : ℝ))*d := by ring
      _ ≤ (remaining.card : ℝ)*d := mul_le_mul_of_nonneg_right hcard hd.le
      _ = ∑ _i ∈ remaining, d := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
        rw [hw n i]
        exact hbound _ (samplePoint_mem grid i)
  | power c beta eta =>
    have hb := hp.2.2.2.1.2.1
    obtain ⟨d, hd, hfloor⟩ := hp.right_remaining_rate_floor
    refine ⟨d*eps^(beta+1), mul_pos hd (Real.rpow_pos_of_pos heps _), ?_⟩
    intro grid w hw n hn remaining hcard
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hpow := Real.rpow_le_rpow (mul_pos heps hnR).le hcard
      (show 0 ≤ beta+1 by linarith)
    have heq : (n : ℝ)^(-beta)*(n : ℝ)^(beta+1) = (n : ℝ) := by
      rw [← Real.rpow_add hnR, show -beta+(beta+1) = (1 : ℝ) by ring, Real.rpow_one]
    calc
      _ = d*(n : ℝ)^(-beta)*(eps*(n : ℝ))^(beta+1) := by
        rw [Real.mul_rpow heps.le hnR.le]
        calc
          _ = d*eps^(beta+1)*((n : ℝ)^(-beta)*(n : ℝ)^(beta+1)) := by rw [heq]
          _ = _ := by ring
      _ ≤ d*(n : ℝ)^(-beta)*(remaining.card : ℝ)^(beta+1) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := hfloor grid w hw n hn remaining

/-- The same bound survives any bounded deletion. The rank margin absorbs
the deleted cardinality, rather than assuming a rate estimate after deletion. -/
theorem PowerProfile.interior_remaining_rate_deleted {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → (2 : ℝ)*r ≤ eps*(n : ℝ) →
    ∀ remaining removed : Finset (Fin n), removed.card ≤ r →
      eps*(n : ℝ) ≤ (remaining.card : ℝ) →
      C*(n : ℝ) ≤ ∑ i ∈ remaining \ removed, (w n).rate i := by
  obtain ⟨C, hC, hbound⟩ := hp.interior_remaining_rate (half_pos heps)
  refine ⟨C, hC, ?_⟩
  intro grid w hw n hn hlarge remaining removed hremoved hcard
  apply hbound grid w hw n hn (remaining \ removed)
  have hcount := Finset.le_card_sdiff removed remaining
  have hcountNat : remaining.card ≤ (remaining \ removed).card+removed.card := by omega
  have hcountR : (remaining.card : ℝ) ≤
      ((remaining \ removed).card : ℝ)+(removed.card : ℝ) := by exact_mod_cast hcountNat
  have hremovedR : (removed.card : ℝ) ≤ r := by exact_mod_cast hremoved
  linarith

end Luce.Section6
