import Luce.Section6SurvivalSplit
import Luce.Section6RateTimeLower
import Luce.Section6LeftGapTail
import Luce.Section6RightGapTail

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- A helper for combining a proved rate-time lower bound and a proved
gap-start tail. The concrete endpoint theorems discharge both premises. -/
theorem deleted_survival_envelope_of_bounds {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n) (q : Fin (Finset.univ \ removed).card)
    (p : ℕ) (hp : 1 ≤ p) {t x h A rho d : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h) (hA : 0 ≤ A)
    (hdA : d ≤ A) (hdr : d ≤ rho) (hrate : A*x ≤ w.rate i*t)
    (htail : (exponentialRace w).real {old |
      raceGapStart (compactDeletedClocks removed old) q < t} ≤ Real.exp (-rho*h)) :
    (∫ old, Real.exp (-((p : ℝ)*w.rate i*raceGapStart (compactDeletedClocks removed old) q))
      ∂exponentialRace w) ≤ Real.exp (-d*x)+Real.exp (-d*h) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hrt : 0 ≤ w.rate i*t := (mul_nonneg hA hx).trans hrate
  have hpT : w.rate i*t ≤ (p : ℝ)*w.rate i*t := by nlinarith
  have hdx : d*x ≤ (p : ℝ)*w.rate i*t :=
    (mul_le_mul_of_nonneg_right hdA hx).trans (hrate.trans hpT)
  exact (deleted_survival_split w removed i q p t).trans
    (add_le_add (Real.exp_le_exp.mpr (by linarith))
      (htail.trans (Real.exp_le_exp.mpr (by nlinarith))))

theorem PowerProfile.left_survival_envelope {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ d H delta : ℝ, 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ (removed : Finset (Fin n)) (i : Fin n), ((i.val : ℝ)+1)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p →
    Nat.dist q.val (h-1) ≤ r+1 →
    (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*raceGapStart (compactDeletedClocks removed old) q))
      ∂exponentialRace (w n)) ≤
      Real.exp (-d*((h : ℝ)/((i.val : ℝ)+1))^alpha)+Real.exp (-d*(h : ℝ)) := by
  obtain ⟨k, H, rho, hk, hk1, hH, hrho, htail⟩ := hp.left_gap_start_lower_tail
  obtain ⟨delta, hd, hd1, hrate⟩ := hp.left_marked_rate_time_lower
  have hc : 0 < c := hp.2.2.1.1
  have hA : 0 < (c/2)*k := mul_pos (by positivity) hk
  refine ⟨min ((c/2)*k) rho, H, delta, lt_min hA hrho, hH, hd, hd1, ?_⟩
  intro grid w hw n r h hn hhH hh hsmall removed i hi q p hpp hshift
  have hhpos : 0 < h := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhn : h ≤ n := Nat.le_of_lt (Nat.cast_lt.mp ((div_lt_one hnR).mp (hsmall.trans hd1)))
  exact deleted_survival_envelope_of_bounds (w n) removed i q p hpp
    (Real.rpow_nonneg (by positivity) _) (Nat.cast_nonneg h) hA.le
    (min_le_left _ _) (min_le_right _ _) (hrate grid w hw n i h k hhpos hk.le hi)
    (htail grid w hw n r h hn hhn hhH hh removed q hshift)

theorem PowerProfile.right_survival_envelope {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ d H delta : ℝ, 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p →
    Nat.dist q.val (n-h) ≤ r+1 →
    (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*raceGapStart (compactDeletedClocks removed old) q))
      ∂exponentialRace (w n)) ≤
      Real.exp (-d*((terminalDepth i : ℝ)/(h : ℝ))^beta)+Real.exp (-d*(h : ℝ)) := by
  obtain ⟨k, H, delta, rho, hk, hk1, hH, hd, hd1, hrho, htail⟩ := hp.right_gap_start_lower_tail r
  obtain ⟨C, hC, hrate⟩ := hp.right_marked_rate_time_lower
  have hA : 0 < C*k := mul_pos hC hk
  refine ⟨min (C*k) rho, H, delta, lt_min hA hrho, hH, hd, hd1, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved i q p hpp hshift
  have hhpos : 0 < h := by omega
  exact deleted_survival_envelope_of_bounds (w n) removed i q p hpp
    (Real.rpow_nonneg (by positivity) _) (Nat.cast_nonneg h) hA.le
    (min_le_left _ _) (min_le_right _ _) (hrate grid w hw n i h k hhpos hk.le)
    (htail grid w hw n h hn hhH hh hsmall removed hremoved q hshift)

end Luce.Section6
