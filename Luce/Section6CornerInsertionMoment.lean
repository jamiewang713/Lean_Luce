import Luce.Section6LocalCornerData
import Luce.Section6InsertionMoments

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Lemma 6.3 in the literal local-kernel notation, with every
moderate-edge and rank-shift premise exposed. -/
theorem PowerProfile.corner_moderate_insertion_moment {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (r p0 : ℕ) (hp0 : 0 < p0) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (side : Corner) (hactive : (cornerBehavior left right side).active) :
    ∃ C d M delta : ℝ, 0 < C ∧ 0 < d ∧ 0 < M ∧ 0 < delta ∧ delta < 1 ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ n (i j : Fin n), M ≤ (cornerDistance side i : ℝ) → M ≤ (cornerDistance side j : ℝ) →
        (cornerDistance side i : ℝ)/(n : ℝ) ≤ delta → (cornerDistance side j : ℝ)/(n : ℝ) ≤ delta →
      ∀ removed : Finset (Fin n), removed.card ≤ r →
      ∀ (k : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
        Nat.dist k.val j.val ≤ r+1 →
        localCornerRatio side (cornerBehavior left right side) (cornerDistance side i) (cornerDistance side j) ≤
          (min (cornerDistance side i : ℝ) (cornerDistance side j : ℝ))^v →
        eLpNorm (fun old => (deletedGapKernel (w n) removed old i k.val).toReal)
          (p : ℝ≥0∞) (exponentialRace (w n)) ≤
          ENNReal.ofReal (C*localEnvelopeKernel side (cornerBehavior left right side) d
            (cornerDistance side i) (cornerDistance side j)) := by
  cases side with
  | left =>
    cases left with
    | finite c => exact False.elim hactive
    | power c alpha eta =>
      obtain ⟨C, d, nu, nt, M, delta, hC, hd, _, _, _, hM, hdelta, hdelta1, hlp, _⟩ :=
        hp.left_insertion_moments r p0 hp0 v hv hv1
      refine ⟨C, d, M, delta, hC, hd, hM, hdelta, hdelta1, ?_⟩
      intro grid w hw n i j hi hj his hjs removed hr k p hp hp' hk hmoderate
      have hh := hlp grid w hw n (j.val+1) (Nat.zero_lt_of_lt j.isLt)
        (by simpa [cornerDistance] using hj) (by simpa [cornerDistance] using hjs)
        removed hr i (by simpa [cornerDistance] using hi) (by simpa [cornerDistance] using his)
        k p hp hp' (by simpa using hk)
      simp only [cornerDistance, cornerBehavior, localCornerRatio, localCornerExponent,
        Nat.cast_add, Nat.cast_one] at hmoderate
      simpa only [cornerDistance, cornerBehavior, localEnvelopeKernel, localCornerRatio,
        localCornerExponent, Nat.cast_add, Nat.cast_one, if_pos hmoderate, add_zero] using hh
  | right =>
    cases right with
    | finite c => exact False.elim hactive
    | power c beta eta =>
      obtain ⟨C, d, nu, nt, M, delta, hC, hd, _, _, _, hM, hdelta, hdelta1, hlp, _⟩ :=
        hp.right_insertion_moments r p0 hp0 v hv hv1
      refine ⟨C, d, M, delta, hC, hd, hM, hdelta, hdelta1, ?_⟩
      intro grid w hw n i j hi hj his hjs removed hr k p hp hp' hk hmoderate
      have hjid : n-terminalDepth j = j.val := by unfold terminalDepth; omega
      have hh := hlp grid w hw n (terminalDepth j) (Nat.zero_lt_of_lt j.isLt)
        hj hjs removed hr i hi his k p hp hp' (by simpa only [hjid] using hk)
      change ((terminalDepth i : ℝ)/(terminalDepth j : ℝ))^beta ≤
        (min (terminalDepth i : ℝ) (terminalDepth j : ℝ))^v at hmoderate
      split_ifs at hh
      simpa only [add_zero, localEnvelopeKernel, localCornerRatio,
        localCornerExponent, cornerBehavior, cornerDistance, terminalDepth] using hh

end Luce.Section6
