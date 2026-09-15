import Luce.Section5MarkedExpectation
import Luce.Section5GapReservoir

/-!
# The bounded marked local estimate

Source: `fixed_points.tex:1035–1048`, equation
`eq:bounded-marked-asymptotic`. The finite gap-selection conditions below
come from sorted separated ranks. All analytic assumptions used by the
finite Taylor and expectation lemmas are discharged from the paper's
standing normalization and profile convergence here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology BigOperators

namespace Luce
set_option backward.isDefEq.respectTransparency false

/-- Uniform local estimate in sorted-rank notation. No convergence,
moment, rate reservoir, or independence premise remains. The explicit
finite gap indices are derived from separated ranks in the next step. -/
theorem section5_sorted_marked_asymptotic
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ u j : Fin r → Fin n, Injective u → StrictMono j →
        ∀ q : Fin r ↪ Fin (Finset.univ \ Finset.univ.image u).card,
          StrictMono (fun a => (q a).val) → (∀ a, (q a).val + a.val = (j a).val) →
            (∀ a, (w n).rate (u a) ≤ M) → (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
              |(n : ℝ) ^ r * (exponentialRace (w n)).real {old | MarkedRankCylinder u j old} -
                ∏ a, profileGapCoefficient f ((w n).rate (u a))
                  (((j a).val + (1 : ℝ)) / n)| < ε := by
  obtain ⟨b, hb, hrest⟩ := hf.deleted_suffix_rate_uniform_lower r hα
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (2 * (r : ℝ) / n) * (M / b) ^ (r + 1) < ε / 2 := by
    have hl := ((tendsto_const_nhds (x := 2 * (r : ℝ))).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))).mul_const ((M / b) ^ (r + 1))
    simp only [zero_mul] at hl
    exact hl.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hrest, hsmall, eventually_gt_atTop 0,
    section5_marked_coefficient_expectation w f hnorm hf r hα M hM (ε / 2) (half_pos hε)]
    with n hn hsn hn0 he u j hu hj q hq hindex huM hjα
  have hr : (Finset.univ.image u).card ≤ r := by
    classical
    rw [Finset.card_image_of_injective _ hu]
    simp
  have hqα (a : Fin r) : ((q a).val : ℝ) ≤ α * n := by
    have hqj : (q a).val ≤ (j a).val := by have hh := hindex a; omega
    have hqj' : ((q a).val : ℝ) ≤ (j a).val := by exact_mod_cast hqj
    linarith [hjα a]
  have hW : ∀ σ : Equiv.Perm (Fin (Finset.univ \ Finset.univ.image u).card), ∀ a,
      b * n ≤ orderedRemainingRate (compactDeletedWeights (w n) (Finset.univ.image u)) σ (q a) :=
    fun σ a => hn (Finset.univ.image u) hr (q a) (hqα a) σ
  have hv : ValidMarkedGapConfiguration (w n) α M (Finset.univ.image u) u j q :=
    ⟨hr, fun a => ⟨hindex a, hjα a, huM a⟩⟩
  have hE := he (Finset.univ.image u) u j q hv
  have hTaylor := markedRankCylinder_taylor_expectation (w n) u j hu hj q hq hindex
    hn0 hb hM huM hW
  have hInt := (markedGap_taylor_expectation (w n) (Finset.univ.image u) u q
    hn0 hb hM huM hW).1
  have hY : Integrable (fun old => ∏ a, markedNormalizedGaps (w n) (Finset.univ.image u) q old a)
      (exponentialRace (w n)) := by
    simpa only [pow_one] using
      integrable_markedNormalizedGaps_mixed (w n) (Finset.univ.image u) q (fun _ => 1)
  have hY0 : ∀ᵐ old ∂exponentialRace (w n),
      0 ≤ ∏ a, markedNormalizedGaps (w n) (Finset.univ.image u) q old a := by
    filter_upwards [exponentialRace_injective_ae (w n), exponentialRace_nonnegative_background (w n)]
      with old hold hpos
    apply Finset.prod_nonneg
    intro a _
    exact raceNormalizedGaps_nonneg (compactDeletedWeights (w n) (Finset.univ.image u))
      (compactDeletedClocks (Finset.univ.image u) old)
      (compactDeletedClocks_injective _ old hold)
      (fun k => hpos (deletedClockLabel _ k)) (q a)
  have hIntError := abs_integral_coefficient_mul_sub_le
    (B := ∏ a, profileGapCoefficient f ((w n).rate (u a)) (((j a).val + (1 : ℝ)) / n))
    hInt hY hY0 (integral_markedNormalizedGaps_prod (w n) (Finset.univ.image u) q)
  have htri := abs_sub_le
    ((n : ℝ) ^ r * (exponentialRace (w n)).real {old | MarkedRankCylinder u j old})
    (∫ old, markedGapCoefficient (w n) (Finset.univ.image u) u q old *
      ∏ a, markedNormalizedGaps (w n) (Finset.univ.image u) q old a ∂exponentialRace (w n))
    (∏ a, profileGapCoefficient f ((w n).rate (u a)) (((j a).val + (1 : ℝ)) / n))
  linarith

end Luce
