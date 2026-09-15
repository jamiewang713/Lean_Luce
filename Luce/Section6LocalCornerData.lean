import Luce.Section6CrossDepthProfile
import Luce.Section6ProfileJointWindow
import Luce.Section6LocalKernelDefinitions

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

def cornerQuantileTime (side : Corner) {n : ℕ} (w : Weights n) (h : ℕ) : ℝ :=
  match side with
  | .left => leftQuantileTime w h
  | .right => rightQuantileTime w h

def localGapDepth (side : Corner) (N q : ℕ) : ℝ :=
  match side with
  | .left => q
  | .right => (N : ℝ)-(q : ℝ)

theorem cornerDistance_positive (side : Corner) {n : ℕ} (i : Fin n) :
    0 < cornerDistance side i := by cases side <;> simp only [cornerDistance] <;> omega

theorem cornerQuantileTime_positive (side : Corner) {n h : ℕ} (w : Weights n)
    (hh : 0 < h) (hhn : h < n) : 0 < cornerQuantileTime side w h := by
  cases side
  · exact (leftQuantileTime_spec w hh hhn).1
  · exact (rightQuantileTime_spec w hh hhn).1

theorem PowerProfile.local_corner_parameters_pos {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (side : Corner)
    (hactive : (cornerBehavior left right side).active) :
    0 < localCornerExponent (cornerBehavior left right side) ∧
    0 < localCornerQ side (cornerBehavior left right side) := by
  cases side with
  | left =>
    cases left with
    | finite c => exact False.elim hactive
    | power c alpha eta =>
      have ha := hp.2.2.1.2.1
      have ha0 := zero_lt_one.trans ha
      have hG : 0 < Real.Gamma (1-1/alpha) := by
        apply Real.Gamma_pos_of_pos
        have hi := one_div_lt_one_div_of_lt zero_lt_one ha
        rw [div_one] at hi
        linarith
      exact ⟨ha0, Real.rpow_pos_of_pos hG _⟩
  | right =>
    cases right with
    | finite c => exact False.elim hactive
    | power c beta eta =>
      have hb := hp.2.2.2.1.2.1
      exact ⟨hb, Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (by positivity)) _⟩

theorem localCornerRatio_positive (side : Corner) (behavior : EndpointBehavior)
    {a h : ℕ} (ha : 0 < a) (hh : 0 < h) : 0 < localCornerRatio side behavior a h := by
  cases side <;> unfold localCornerRatio <;> positivity

theorem localEnvelopeKernel_positive (side : Corner) (behavior : EndpointBehavior) (d : ℝ)
    {a h : ℕ} (ha : 0 < a) (hh : 0 < h) : 0 < localEnvelopeKernel side behavior d a h := by
  have hx := localCornerRatio_positive side behavior ha hh
  unfold localEnvelopeKernel
  positivity

theorem localEnvelopeKernel_antitone (side : Corner) (behavior : EndpointBehavior)
    {a h : ℕ} (ha : 0 < a) (hh : 0 < h) {d D : ℝ} (hd : d ≤ D) :
    localEnvelopeKernel side behavior D a h ≤ localEnvelopeKernel side behavior d a h := by
  have hx := localCornerRatio_positive side behavior ha hh
  unfold localEnvelopeKernel
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hd hx.le]

theorem localIdealKernel_nonneg (side : Corner) (behavior : EndpointBehavior)
    (hg : 0 ≤ localCornerExponent behavior) (hq : 0 ≤ localCornerQ side behavior)
    {a h : ℕ} (ha : 0 < a) (hh : 0 < h) : 0 ≤ localIdealKernel side behavior a h := by
  have hx := localCornerRatio_positive side behavior ha hh
  unfold localIdealKernel
  positivity

theorem localIdealKernel_le_envelope (side : Corner) (behavior : EndpointBehavior)
    (hg : 0 ≤ localCornerExponent behavior) (hq : 0 ≤ localCornerQ side behavior)
    {a h : ℕ} (ha : 0 < a) (hh : 0 < h) {d : ℝ} (hd : d ≤ localCornerQ side behavior) :
    localIdealKernel side behavior a h ≤
      (localCornerExponent behavior*localCornerQ side behavior)*localEnvelopeKernel side behavior d a h := by
  have hx := localCornerRatio_positive side behavior ha hh
  unfold localIdealKernel localEnvelopeKernel
  have he : Real.exp (-localCornerQ side behavior*localCornerRatio side behavior a h) ≤
      Real.exp (-d*localCornerRatio side behavior a h) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hd hx.le]
  have hb := mul_le_mul_of_nonneg_left he
    (by positivity : 0 ≤ localCornerExponent behavior*localCornerQ side behavior*localCornerRatio side behavior a h/(h : ℝ))
  exact hb.trans_eq (by ring)

/-- A single interface for the two proved endpoint asymptotics. -/
theorem PowerProfile.corner_cross_depth_relative_error {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (grid : SamplingGrid) (w : WeightArray) (hw : SampledRates grid w f)
    (side : Corner) (hactive : (cornerBehavior left right side).active) :
    ∃ rho C delta M : ℝ, 0 < rho ∧ 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧ 1 ≤ M ∧
      ∀ n (i j : Fin n), M ≤ (cornerDistance side i : ℝ) → M ≤ (cornerDistance side j : ℝ) →
        (cornerDistance side i : ℝ)/(n : ℝ) < delta → (cornerDistance side j : ℝ)/(n : ℝ) < delta →
        let behavior := cornerBehavior left right side
        let x := localCornerRatio side behavior (cornerDistance side i) (cornerDistance side j)
        let q := localCornerQ side behavior
        let t := cornerQuantileTime side (w n) (cornerDistance side j)
        let e := crossDepthError rho n (cornerDistance side i) (cornerDistance side j)
        |(w n).rate i*t/(q*x)-1| ≤ C*e ∧
        |((w n).rate i/((n : ℝ)*populationD (w n) 1 t))/
          (localCornerExponent behavior*q*x/(cornerDistance side j : ℝ))-1| ≤ C*e := by
  cases side with
  | left =>
    cases left with
    | finite c => exact False.elim hactive
    | power c alpha eta =>
      simpa only [cornerBehavior, cornerDistance, cornerQuantileTime, localCornerRatio,
        localCornerExponent, localCornerQ, Nat.cast_add, Nat.cast_one] using
        hp.left_cross_depth_relative_error grid w hw
  | right =>
    cases right with
    | finite c => exact False.elim hactive
    | power c beta eta =>
      exact hp.right_cross_depth_relative_error grid w hw

/-- One interface for the actual time/weight events in either active
corner. The gap depth is the exact depth in the deleted race. -/
theorem PowerProfile.corner_joint_quantile_window {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (side : Corner) (hactive : (cornerBehavior left right side).active) :
    ∃ a V K u0 delta M : ℝ,
      0 < a ∧ a ≤ 1 ∧ 0 < V ∧ 0 < K ∧ 0 < u0 ∧ u0 ≤ 1/2 ∧ 0 < delta ∧ 0 < M ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ n m r : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      ∀ removed : Finset (Fin n), removed.card ≤ r →
      ∀ q : Fin (Finset.univ \ removed).card,
        |localGapDepth side (Finset.univ \ removed).card q.val-(m : ℝ)| ≤ r →
      ∀ u : ℝ, 0 < u → u ≤ u0 → 8*(r : ℝ) ≤ a*u*m →
        let t := cornerQuantileTime side (w n) m
        (exponentialRace (w n)).real {old |
          u < |raceGapStart (compactDeletedClocks removed old) q/t-1| ∨
          V*u < |raceGapRate (compactDeletedWeights (w n) removed)
            (compactDeletedClocks removed old) q/((n : ℝ)*populationD (w n) 1 t)-1|} ≤
          K/(u^2*(m : ℝ)) := by
  cases side with
  | left =>
    cases left with
    | finite c => exact False.elim hactive
    | power c alpha eta => exact hp.left_joint_quantile_window
  | right =>
    cases right with
    | finite c => exact False.elim hactive
    | power c beta eta => exact hp.right_joint_quantile_window

end Luce.Section6
