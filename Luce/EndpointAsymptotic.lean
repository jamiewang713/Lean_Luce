import Luce.EndpointTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.LiminfLimsup

/-! # The epsilon endpoint estimate

A deterministic linear cutoff `B = β(n+1)` yields the same asymptotic bound
as the square-root cutoff in the paper. Choosing `β = sqrt ε` recovers the
power `ε^(γ/4)` exactly, while avoiding any rounding issue in `ceil (ε(n+1))`.
-/

open scoped BigOperators Topology
open Real Set MeasureTheory Filter

namespace Luce

noncomputable section

/-- The `m`th label counted back from the last label. -/
def terminalCandidate (n m : ℕ) : Fin (n + 1) :=
  ⟨n - (m - 1), Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

lemma terminalCandidate_val_add {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n + 1) :
    (terminalCandidate n m).val + m = n + 1 := by
  simp only [terminalCandidate]
  omega

/-- Expected fixed points in the last `ceil (ε(n+1))` positions. -/
def epsilonTailExpectation (w : (n : ℕ) → Weights (n + 1)) (ε : ℝ) (n : ℕ) : ℝ :=
  ∫ clocks, (terminalFixedPointCount (terminalCandidate n) ⌈ε * (n + 1)⌉₊ clocks : ℝ)
    ∂exponentialRace (w n)

lemma epsilonTailExpectation_nonneg (w : (n : ℕ) → Weights (n + 1)) (ε : ℝ) (n : ℕ) :
    0 ≤ epsilonTailExpectation w ε n := integral_nonneg (fun _ => Nat.cast_nonneg _)

lemma tendsto_nat_add_one : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop

/-- The expectation bound is eventually valid with a linear cutoff whenever
`2 ε < β` and the cutoff stays beyond `1/γ`. -/
theorem epsilonTailExpectation_eventually_le
    (w : (n : ℕ) → Weights (n + 1))
    (hnorm : ∀ n, ∑ i, (w n).rate i = ((n + 1 : ℕ) : ℝ))
    {ε β γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (hgap : 2 * ε < β)
    (hβone : β ≤ 1) (hβsmall : β ≤ Real.exp (-2 / γ) / 2)
    (hrate : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε * (n + 1)⌉₊,
      γ ≤ (w n).rate (terminalCandidate n m)) :
    ∀ᶠ n in atTop, epsilonTailExpectation w ε n ≤
      (ε * (n + 1) + 1) * Real.exp (-(bernoulliLowerTailConstant / 2) * (β * (n + 1))) +
        2 * (2 * β) ^ (γ / 2) := by
  have hβ : 0 < β := by linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, 3 ≤ (β - 2 * ε) * (n + 1) :=
    (Tendsto.const_mul_atTop (sub_pos.mpr hgap) tendsto_nat_add_one).eventually_ge_atTop 3
  filter_upwards [hlarge, hrate] with n hnlarge hnrate
  have hN : (0 : ℝ) < n + 1 := by positivity
  let M : ℕ := ⌈ε * (n + 1)⌉₊
  have hceil : (M : ℝ) < ε * (n + 1) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hM : 1 ≤ M := Nat.ceil_pos.mpr (by positivity)
  have hBM : 2 * (M : ℝ) ≤ β * (n + 1) - 1 := by nlinarith
  have hMn : M ≤ n + 1 := by
    have hcast : (M : ℝ) ≤ (n : ℝ) + 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hβone) hN.le]
    exact_mod_cast hcast
  have hBpos : 0 < β * ((n : ℝ) + 1) := mul_pos hβ hN
  have hBle : β * ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using mul_le_of_le_one_left hN.le hβone
  obtain ⟨s, ⟨hs0, hcut⟩, _⟩ := exists_unique_meanSurvivors_cutoff
    (Nat.succ_pos n) (w n).rate (w n).positive hBpos hBle
  have hS := meanSurvivors_lower_bound (w n).rate (fun i => ((w n).positive i).le)
    (hnorm n) (show 0 ≤ 1 / γ by positivity)
  have hSge : β * (n + 1) ≤ meanSurvivors (w n).rate (1 / γ) := by
    simp only [Nat.cast_add, Nat.cast_one] at hS
    have he : -2 * (1 / γ) = -2 / γ := by ring
    rw [he] at hS
    nlinarith [mul_nonneg (sub_nonneg.mpr hβsmall) hN.le]
  have hsge : 1 / γ ≤ s := by
    by_contra hbad
    have hstrict := meanSurvivors_strictAnti (Nat.succ_pos n) (w n).rate (w n).positive
      (lt_of_not_ge hbad)
    rw [hcut] at hstrict
    exact not_lt_of_ge hSge hstrict
  have hγs : 1 ≤ γ * s := by
    have h := mul_le_mul_of_nonneg_left hsge hγ.le
    have hg : γ * (1 / γ) = 1 := by field_simp
    rwa [hg] at h
  have hbound := endpoint_fixedPoint_expectation_power_bound (w n) (hnorm n)
    (terminalCandidate n) hM
    (fun m hm => terminalCandidate_val_add (Finset.mem_Icc.mp hm).1
      ((Finset.mem_Icc.mp hm).2.trans hMn)) hγ hnrate hcut hBM hγs
  have hratio : 2 * (β * ((n : ℝ) + 1)) / ((n : ℝ) + 1) = 2 * β := by
    field_simp
  rw [hratio] at hbound
  apply hbound.trans
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_right hceil.le (Real.exp_pos _).le

/-- The rounded linear prefactor is dominated by exponential decay. -/
lemma tendsto_endpoint_early_envelope {ε β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n : ℕ => (ε * (n + 1) + 1) *
      Real.exp (-(bernoulliLowerTailConstant / 2) * (β * (n + 1)))) atTop (𝓝 0) := by
  let a := (bernoulliLowerTailConstant / 2) * β
  have ha : 0 < a := by dsimp [a]; positivity [bernoulliLowerTailConstant_pos]
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-a * (n + 1))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha).comp tendsto_nat_add_one
  have h0 : Tendsto (fun n : ℕ => Real.exp (-a * (n + 1))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_neg_of_pos ha) tendsto_nat_add_one)
  have h := (h1.const_mul ε).add h0
  simp only [mul_zero, add_zero] at h
  convert h using 1
  funext n
  dsimp [a]
  rw [show -(bernoulliLowerTailConstant / 2) * (β * ((n : ℝ) + 1)) =
    -((bernoulliLowerTailConstant / 2) * β) * (n + 1) by ring]
  ring

/-- The endpoint limsup bound for any admissible linear cutoff fraction. -/
theorem epsilonTailExpectation_limsup_le
    (w : (n : ℕ) → Weights (n + 1))
    (hnorm : ∀ n, ∑ i, (w n).rate i = ((n + 1 : ℕ) : ℝ))
    {ε β γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (hgap : 2 * ε < β)
    (hβone : β ≤ 1) (hβsmall : β ≤ Real.exp (-2 / γ) / 2)
    (hrate : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε * (n + 1)⌉₊,
      γ ≤ (w n).rate (terminalCandidate n m)) :
    limsup (epsilonTailExpectation w ε) atTop ≤ 2 * (2 * β) ^ (γ / 2) := by
  have hβ : 0 < β := by linarith
  have hlim := (tendsto_endpoint_early_envelope (ε := ε) hβ).add_const (2 * (2 * β) ^ (γ / 2))
  simp only [zero_add] at hlim
  have hbounded : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (ε * (n + 1) + 1) *
        Real.exp (-(bernoulliLowerTailConstant / 2) * (β * (n + 1))) +
          2 * (2 * β) ^ (γ / 2)) := by
    refine ⟨2 * (2 * β) ^ (γ / 2) + 1, ?_⟩
    exact (hlim.eventually (Iio_mem_nhds (by linarith))).mono (fun _ h => h.le)
  exact (limsup_le_limsup
    (epsilonTailExpectation_eventually_le w hnorm hε hγ hgap hβone hβsmall hrate)
    (isCoboundedUnder_le_of_le atTop (epsilonTailExpectation_nonneg w ε)) hbounded).trans_eq hlim.limsup_eq

/-- The exact power and constant in equation `eq:tail-epsilon`. -/
theorem epsilonTailExpectation_power_limsup
    (w : (n : ℕ) → Weights (n + 1))
    (hnorm : ∀ n, ∑ i, (w n).rate i = ((n + 1 : ℕ) : ℝ))
    {ε γ : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 4) (hγ : 0 < γ)
    (hcutoff : Real.sqrt ε ≤ Real.exp (-2 / γ) / 2)
    (hrate : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε * (n + 1)⌉₊,
      γ ≤ (w n).rate (terminalCandidate n m)) :
    limsup (epsilonTailExpectation w ε) atTop ≤
      (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4) := by
  have hroot : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hrootSmall : Real.sqrt ε < 1 / 2 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by norm_num; exact hεsmall)
  have hgap : 2 * ε < Real.sqrt ε := by
    nlinarith [Real.sq_sqrt hε.le]
  have hbound := epsilonTailExpectation_limsup_le w hnorm hε hγ hgap
    (by linarith : Real.sqrt ε ≤ 1) hcutoff hrate
  have hpower : 2 * (2 * Real.sqrt ε) ^ (γ / 2) =
      (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4) := by
    rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg ε), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hε.le, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    rw [show (1 / 2 : ℝ) * (γ / 2) = γ / 4 by ring]
    ring
  rwa [hpower] at hbound

/-- A uniform rate lower bound on one fixed terminal neighborhood implies
the paper's epsilon estimate for every sufficiently small positive epsilon. -/
theorem endpoint_epsilon_estimate
    (w : (n : ℕ) → Weights (n + 1))
    (hnorm : ∀ n, ∑ i, (w n).rate i = ((n + 1 : ℕ) : ℝ))
    {γ ε₀ : ℝ} (hγ : 0 < γ) (hε₀ : 0 < ε₀)
    (hrate : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε₀ * (n + 1)⌉₊,
      γ ≤ (w n).rate (terminalCandidate n m)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      limsup (epsilonTailExpectation w ε) atTop ≤
        (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4) := by
  let δ := min ε₀ (min (1 / 4 : ℝ) (Real.exp (-2 / γ) / 2) ^ 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min hε₀
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hεε₀ : ε ≤ ε₀ := (hεδ.trans_le (min_le_left _ _)).le
  have hεmin : ε < (min (1 / 4 : ℝ) (Real.exp (-2 / γ) / 2)) ^ 2 :=
    hεδ.trans_le (min_le_right _ _)
  have hminpos : 0 < min (1 / 4 : ℝ) (Real.exp (-2 / γ) / 2) := by positivity
  have hroot : Real.sqrt ε < min (1 / 4 : ℝ) (Real.exp (-2 / γ) / 2) :=
    (Real.sqrt_lt' hminpos).mpr hεmin
  have hεsmall : ε < 1 / 4 := by
    have hrootSmall := hroot.trans_le (min_le_left _ _)
    nlinarith [Real.sqrt_nonneg ε, Real.sq_sqrt hε.le]
  apply epsilonTailExpectation_power_limsup w hnorm hε hεsmall hγ
    (hroot.trans_le (min_le_right _ _)).le
  filter_upwards [hrate] with n hn
  intro m hm
  apply hn m
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
    (Finset.mem_Icc.mp hm).2.trans (Nat.ceil_mono (mul_le_mul_of_nonneg_right hεε₀ (by positivity)))⟩

end

end Luce
