import Luce.Section6CriticalProbeTimes

noncomputable section
namespace Luce.Section6

theorem critical_probe_arrival_upper {G c C k m z : ℝ}
    (hc : 0 < c) (hk : 0 < k) (hm : 0 ≤ m) (hz : 1 ≤ z)
    (hC : C+c*|Real.log k| ≤ c*z)
    (hG : |G-(c*k*m/z)*(z+Real.log z-Real.log k)| ≤ C*k*m/z+1) :
    G ≤ 3*c*k*m+1 := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hlog := Real.log_le_self hz0.le
  have hclog := mul_le_mul_of_nonneg_left hlog hc.le
  have hab := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log k)) hc.le
  have hbracket : c*(z+Real.log z-Real.log k)+C ≤ 3*c*z := by linarith
  calc
    G ≤ (c*k*m/z)*(z+Real.log z-Real.log k)+(C*k*m/z+1) := by
      have := (abs_le.mp hG).2; linarith
    _ = (k*m/z)*(c*(z+Real.log z-Real.log k)+C)+1 := by ring
    _ ≤ (k*m/z)*(3*c*z)+1 := add_le_add
      (mul_le_mul_of_nonneg_left hbracket (by positivity)) le_rfl
    _ = _ := by field_simp

theorem critical_probe_arrival_lower {G c C k m z : ℝ}
    (hc : 0 < c) (hk : 0 < k) (hm : 0 ≤ m) (hz : 1 ≤ z)
    (hC : C+c*|Real.log k| ≤ c*z/2)
    (hG : |G-(c*k*m/z)*(z+Real.log z-Real.log k)| ≤ C*k*m/z+1) :
    c*k*m/2-1 ≤ G := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hclog := mul_nonneg hc.le (Real.log_nonneg hz)
  have hab := mul_le_mul_of_nonneg_left (le_abs_self (Real.log k)) hc.le
  have hbracket : c*z/2 ≤ c*(z+Real.log z-Real.log k)-C := by linarith
  calc
    _ = (k*m/z)*(c*z/2)-1 := by field_simp
    _ ≤ (k*m/z)*(c*(z+Real.log z-Real.log k)-C)-1 := sub_le_sub_right
      (mul_le_mul_of_nonneg_left hbracket (by positivity)) _
    _ = (c*k*m/z)*(z+Real.log z-Real.log k)-(C*k*m/z+1) := by ring
    _ ≤ G := by have := (abs_le.mp hG).1; linarith

/-- Two explicit probe times bracket the mth arrival with fixed relative
margins. Their constants depend only on the critical profile. -/
theorem CriticalProfile.probe_brackets {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ Z : ℝ, 1 ≤ Z ∧ ∀ (grid : SamplingGrid) (w : WeightArray),
      SampledRates grid w f → ∀ (n m : ℕ), 4 ≤ m → m ≤ n →
      Z ≤ Real.log ((n : ℝ)/m) →
      (n : ℝ)*populationG (w n) (criticalProbeTime n m (1/(16*c))) ≤ (m : ℝ)/2 ∧
      2*(m : ℝ) ≤ (n : ℝ)*populationG (w n) (criticalProbeTime n m (8/c)) := by
  obtain ⟨C,hC,hbounds⟩ := hp.probe_estimates
  have hc : 0 < c := hp.2.2.1
  let l : ℝ := 1/(16*c)
  let u : ℝ := 8/c
  have hl : 0 < l := by dsimp [l]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  let Z := max 1 (max l (max u (2*(C+c*|Real.log l|+c*|Real.log u|)/c)))
  refine ⟨Z,le_max_left _ _,?_⟩
  intro grid w hw n m hm hmn hz
  have hz1 : 1 ≤ Real.log ((n : ℝ)/m) := (le_max_left _ _).trans hz
  have hlz : l ≤ Real.log ((n : ℝ)/m) := (le_max_left _ _).trans ((le_max_right _ _).trans hz)
  have huz : u ≤ Real.log ((n : ℝ)/m) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hz))
  have hZ : 2*(C+c*|Real.log l|+c*|Real.log u|) ≤ c*Real.log ((n : ℝ)/m) := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hz))
    simpa only [mul_comm] using (div_le_iff₀ hc).mp h
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hnl := (hbounds grid w hw n m (by omega) hmn l hl hlz).1
  have hnu := (hbounds grid w hw n m (by omega) hmn u hu huz).1
  constructor
  · have h := critical_probe_arrival_upper hc hl hm0 hz1 (by
      nlinarith [mul_nonneg hc.le (abs_nonneg (Real.log u)),
        mul_nonneg hc.le (abs_nonneg (Real.log l))]) hnl
    have hcoeff : 3*c*l = 3/16 := by dsimp [l]; field_simp
    rw [hcoeff] at h
    dsimp only [l] at h
    linarith
  · have h := critical_probe_arrival_lower hc hu hm0 hz1 (by
      nlinarith [mul_nonneg hc.le (abs_nonneg (Real.log l))]) hnu
    have hcoeff : c*u = 8 := by dsimp [u]; field_simp
    rw [hcoeff] at h
    dsimp only [u] at h
    linarith

end Luce.Section6
