import Luce.Section6EnvelopeAbsorption
import Luce.Section6UniformMomentDecay

noncomputable section
namespace Luce.Section6

/-- Uniform absorption of the polynomial insertion prefactor into a
stretched exponential. All comparison premises are numerical and explicit;
concrete endpoint uses must prove them from the extreme-set inequalities. -/
theorem extreme_moment_absorption {B d b nu : ℝ} (hB : 0 < B) (hd : 0 < d)
    (hb : 0 ≤ b) (hnu : 0 < nu) (p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ), 1 ≤ p → p ≤ p0 →
    ∀ a z x y m : ℝ, 1 ≤ a → 0 ≤ z → z ≤ a^b → a^nu ≤ x → a^nu ≤ y →
    m ≤ 2*(p.factorial : ℝ)*(B*z)^p*(Real.exp (-d*x)+Real.exp (-d*y)) →
    m ≤ (C*Real.exp (-(d/(2*(p0 : ℝ)))*a^nu))^p := by
  obtain ⟨K, hK, habs⟩ := power_envelope_absorption (a := b*(p0 : ℝ)) hnu.ne'
    (div_nonneg (mul_nonneg hb (Nat.cast_nonneg p0)) hnu.le)
  let T := 4*(p0.factorial : ℝ)*(max 1 B)^p0*K*(1/(d/2))^((b*(p0 : ℝ))/nu)
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨max 1 T, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro p hp hpp a z x y m ha hz hza hx hy hm
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hp0R : (0 : ℝ) < p0 := Nat.cast_pos.mpr hp0
  have hfact : (p.factorial : ℝ) ≤ p0.factorial := by exact_mod_cast Nat.factorial_le hpp
  have hBpow : B^p ≤ (max 1 B)^p0 :=
    (pow_le_pow_left₀ hB.le (le_max_right _ _) p).trans (pow_le_pow_right₀ (le_max_left _ _) hpp)
  have hpow : z^p ≤ a^(b*(p0 : ℝ)) := by
    calc
      _ ≤ (a^b)^p := pow_le_pow_left₀ hz hza p
      _ ≤ (a^b)^p0 := pow_le_pow_right₀ (Real.one_le_rpow ha hb) hpp
      _ = _ := (Real.rpow_mul_natCast ha0.le b p0).symm
  have hcoeff : 2*(p.factorial : ℝ)*(B*z)^p ≤
      2*(p0.factorial : ℝ)*(max 1 B)^p0*a^(b*(p0 : ℝ)) := by
    rw [mul_pow]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hBpow (by positivity : 0 ≤ 2*(p.factorial : ℝ)))
      hpow (pow_nonneg hz _) (by positivity)
    have hc := mul_le_mul_of_nonneg_right (show 2*(p.factorial : ℝ) ≤ 2*(p0.factorial : ℝ) by linarith)
      (mul_nonneg (pow_nonneg (by positivity : 0 ≤ max 1 B) p0) (Real.rpow_nonneg ha0.le (b*(p0 : ℝ))))
    nlinarith
  have hex : Real.exp (-d*x)+Real.exp (-d*y) ≤ 2*Real.exp (-d*a^nu) := by
    have hx' : Real.exp (-d*x) ≤ Real.exp (-d*a^nu) := Real.exp_le_exp.mpr (by nlinarith)
    have hy' : Real.exp (-d*y) ≤ Real.exp (-d*a^nu) := Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hraw : m ≤ T*Real.exp (-(d/2)*a^nu) := by
    have hm' := hm.trans (mul_le_mul hcoeff hex (by positivity) (by positivity))
    have hh := mul_le_mul_of_nonneg_left (habs d a hd ha0)
      (show 0 ≤ 4*(p0.factorial : ℝ)*(max 1 B)^p0 by positivity)
    dsimp [T]
    simp only [neg_mul] at hm' ⊢
    nlinarith
  have hCpow : T ≤ (max 1 T)^p := (le_max_right _ _).trans
    (le_self_pow₀ (le_max_left _ _) (by omega))
  have hscale : (p : ℝ)*(d/(2*(p0 : ℝ))) ≤ d/2 := by
    have hppR : (p : ℝ) ≤ p0 := by exact_mod_cast hpp
    have hh := mul_le_mul_of_nonneg_right hppR (by positivity : 0 ≤ d/(2*(p0 : ℝ)))
    have he : (p0 : ℝ)*(d/(2*(p0 : ℝ))) = d/2 := by field_simp
    rwa [he] at hh
  have he : Real.exp (-(d/2)*a^nu) ≤ (Real.exp (-(d/(2*(p0 : ℝ)))*a^nu))^p := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg ha0.le nu)]
  apply hraw.trans
  simpa only [mul_pow] using (mul_le_mul hCpow he (Real.exp_pos _).le (by positivity))

end Luce.Section6
