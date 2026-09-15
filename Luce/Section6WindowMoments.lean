import Luce.Section6PowerWindowComparison
import Luce.Section6PopulationMomentBounds
import Luce.Section6QuantileComparability

noncomputable section
namespace Luce.Section6

/-- Convert actual power envelopes and the proved center normalization
into both moment estimates. Concrete endpoint applications must discharge
the window and center bounds from their original profile hypotheses. -/
theorem population_moments_from_power_window {k r : ℝ} (hk : 0 < k) (hr : r ≤ 0) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (n : ℕ) (w : Weights n) (m t B : ℝ), 0 < n → 0 < m → 0 < t → 0 < B →
      (∀ s : ℝ, t/8 ≤ s → s ≤ 8*t →
        B*s^r/2 ≤ populationD w 1 s ∧ populationD w 1 s ≤ 2*(B*s^r)) →
      |k*t*populationD w 1 t/(m/(n : ℝ))-1| ≤ 1/2 →
      ∀ s : ℝ, t/4 ≤ s → s ≤ 4*t →
        a*m/t ≤ (n : ℝ)*populationD w 1 s ∧
        (n : ℝ)*populationD w 1 s ≤ C*m/t ∧
        (n : ℝ)*populationD w 2 s ≤ C*m/t^2 := by
  let a := ((8 : ℝ)^r/4)*(1/(2*k))
  let b := (4/(8 : ℝ)^r)*(2/k)
  let d := 8*Real.exp (-1)*b
  have h8 : 0 < (8 : ℝ)^r := Real.rpow_pos_of_pos (by norm_num) _
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨a, b+d, ha, add_pos hb hd, ?_⟩
  intro n w m t B hn hm ht hB hwindow hcenter
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let lead := (m/(n : ℝ))/(k*t)
  have hlead : 0 < lead := div_pos (div_pos hm hnR) (mul_pos hk ht)
  have heq : populationD w 1 t/lead = k*t*populationD w 1 t/(m/(n : ℝ)) := by
    dsimp [lead]
    field_simp
  have hc := half_relative_error_bounds hlead (by rw [heq]; exact hcenter)
  have hcLo : (1/(2*k))*m/t ≤ (n : ℝ)*populationD w 1 t := by
    have hh := mul_le_mul_of_nonneg_left hc.1 hnR.le
    have hid : (n : ℝ)*(lead/2) = (1/(2*k))*m/t := by dsimp [lead]; field_simp
    rwa [hid] at hh
  have hcHi : (n : ℝ)*populationD w 1 t ≤ (2/k)*m/t := by
    have hh := mul_le_mul_of_nonneg_left hc.2 hnR.le
    have hid : (n : ℝ)*(2*lead) = (2/k)*m/t := by dsimp [lead]; field_simp
    rwa [hid] at hh
  have hratio := power_window_comparison hB hr ht hwindow
  have hfirst (v : ℝ) (hvlo : t/8 ≤ v) (hvhi : v ≤ 8*t) :
      a*m/t ≤ (n : ℝ)*populationD w 1 v ∧ (n : ℝ)*populationD w 1 v ≤ b*m/t := by
    have hv := hratio v hvlo hvhi
    constructor
    · calc
        _ = ((8 : ℝ)^r/4)*((1/(2*k))*m/t) := by dsimp [a]; ring
        _ ≤ ((8 : ℝ)^r/4)*((n : ℝ)*populationD w 1 t) := mul_le_mul_of_nonneg_left hcLo (by positivity)
        _ = (n : ℝ)*(((8 : ℝ)^r/4)*populationD w 1 t) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hv.1 hnR.le
    · calc
        _ ≤ (n : ℝ)*((4/(8 : ℝ)^r)*populationD w 1 t) := mul_le_mul_of_nonneg_left hv.2 hnR.le
        _ = (4/(8 : ℝ)^r)*((n : ℝ)*populationD w 1 t) := by ring
        _ ≤ (4/(8 : ℝ)^r)*((2/k)*m/t) := mul_le_mul_of_nonneg_left hcHi (by positivity)
        _ = _ := by dsimp [b]; ring
  intro s hslo hshi
  have hs : 0 < s := (div_pos ht (by norm_num)).trans_le hslo
  have hfs := hfirst s (by linarith) (by linarith)
  refine ⟨hfs.1, hfs.2.trans ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hd.le) hm.le) ht.le
  · have hh := (hfirst (s/2) (by linarith) (by linarith)).2
    have hfactor : Real.exp (-1)/(s/2) ≤ 8*Real.exp (-1)/t := by
      have hh := div_le_div_of_nonneg_left (Real.exp_pos (-1)).le
        (by positivity : 0 < t/8) (by linarith : t/8 ≤ s/2)
      exact hh.trans_eq (by field_simp)
    calc
      _ ≤ (n : ℝ)*((Real.exp (-1)/(s/2))*populationD w 1 (s/2)) :=
        mul_le_mul_of_nonneg_left (populationD_two_le w hs) hnR.le
      _ = (Real.exp (-1)/(s/2))*((n : ℝ)*populationD w 1 (s/2)) := by ring
      _ ≤ (Real.exp (-1)/(s/2))*(b*m/t) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ (8*Real.exp (-1)/t)*(b*m/t) := mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = d*m/t^2 := by dsimp [d]; ring
      _ ≤ (b+d)*m/t^2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hb.le) hm.le) (sq_nonneg t)

end Luce.Section6
