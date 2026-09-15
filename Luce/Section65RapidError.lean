import Luce.Section65CoreDecay

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Luce.Section6

def logWeight65 (n : ℕ) : ℝ := 1+Real.log (n : ℝ)

theorem logWeight65_one_le (n : ℕ) : 1 ≤ logWeight65 n := by
  have := Real.log_natCast_nonneg n
  dsimp [logWeight65]
  linarith

def RapidError65 (f : ℕ → ℝ) : Prop :=
  ∀ K : ℕ, Tendsto (fun n => (logWeight65 n)^K * |f n|) atTop (𝓝 0)

def LogGrowth65 (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ᶠ n in atTop, |a n| ≤ C*(logWeight65 n)^K

theorem RapidError65.tendsto {f : ℕ → ℝ} (h : RapidError65 f) :
    Tendsto f atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  simpa [Function.comp_def] using h 0

theorem RapidError65.congr {f g : ℕ → ℝ} (h : RapidError65 f)
    (he : f =ᶠ[atTop] g) : RapidError65 g := by
  intro K
  apply (h K).congr'
  filter_upwards [he] with n hn
  rw [hn]

theorem rapidError65_zero : RapidError65 (fun _ => 0) := by
  intro K
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem RapidError65.add {f g : ℕ → ℝ} (hf : RapidError65 f) (hg : RapidError65 g) :
    RapidError65 (fun n => f n+g n) := by
  intro K
  have hn (n : ℕ) : 0 ≤ (logWeight65 n)^K := pow_nonneg (by linarith [logWeight65_one_le n]) _
  apply squeeze_zero (fun n => mul_nonneg (hn n) (abs_nonneg _))
    (fun n => (mul_le_mul_of_nonneg_left (abs_add_le (f n) (g n)) (hn n)).trans_eq (mul_add _ _ _))
  simpa using (hf K).add (hg K)

theorem RapidError65.sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (h : ∀ i ∈ s, RapidError65 (f i)) : RapidError65 (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rapidError65_zero
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi] using
      (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

theorem logGrowth65_const (c : ℝ) : LogGrowth65 (fun _ => c) := by
  refine ⟨|c|+1, by positivity, 0, Filter.Eventually.of_forall (fun n => ?_)⟩
  simp

theorem LogGrowth65.mul {a b : ℕ → ℝ} (ha : LogGrowth65 a) (hb : LogGrowth65 b) :
    LogGrowth65 (fun n => a n*b n) := by
  obtain ⟨C,hC,K,ha⟩ := ha
  obtain ⟨D,hD,L,hb⟩ := hb
  refine ⟨C*D,mul_pos hC hD,K+L,?_⟩
  filter_upwards [ha,hb] with n han hbn
  have hw : 0 ≤ logWeight65 n := le_trans zero_le_one (logWeight65_one_le n)
  rw [abs_mul, pow_add]
  calc
    _ ≤ (C*logWeight65 n^K)*(D*logWeight65 n^L) :=
      mul_le_mul han hbn (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem LogGrowth65.pow {a : ℕ → ℝ} (ha : LogGrowth65 a) (k : ℕ) :
    LogGrowth65 (fun n => a n^k) := by
  induction k with
  | zero => simpa using logGrowth65_const 1
  | succ k ih => simpa [pow_succ] using ih.mul ha

theorem RapidError65.mul_growth {f a : ℕ → ℝ} (hf : RapidError65 f) (ha : LogGrowth65 a) :
    RapidError65 (fun n => a n*f n) := by
  obtain ⟨C,hC,d,ha⟩ := ha
  intro K
  have hlim := (hf (K+d)).const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by
    exact mul_nonneg (pow_nonneg (by linarith [logWeight65_one_le n]) _) (abs_nonneg _))) ?_ hlim
  filter_upwards [ha] with n hn
  rw [abs_mul, pow_add]
  have hw : 0 ≤ (logWeight65 n)^K := pow_nonneg (by linarith [logWeight65_one_le n]) _
  calc
    _ ≤ logWeight65 n^K * ((C*logWeight65 n^d)*|f n|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn (abs_nonneg _)) hw
    _ = _ := by ring

theorem RapidError65.const_mul {f : ℕ → ℝ} (hf : RapidError65 f) (c : ℝ) :
    RapidError65 (fun n => c*f n) := hf.mul_growth (logGrowth65_const c)

theorem rapidError65_of_core_bound {f : ℕ → ℝ} {C κ : ℝ} {K : ℕ}
    (hκ : 0 < κ) (h : ∀ᶠ n in atTop, |f n| ≤
      C*(logWeight65 n)^K*(idealCoreLower n : ℝ)^(-κ)) : RapidError65 f := by
  intro L
  have hlim := (core_error_tendsto65 (L+K) hκ).const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    mul_nonneg (pow_nonneg (by linarith [logWeight65_one_le n]) _) (abs_nonneg _))) ?_ hlim
  filter_upwards [h] with n hn
  calc
    _ ≤ logWeight65 n^L * (C*logWeight65 n^K*(idealCoreLower n : ℝ)^(-κ)) :=
      mul_le_mul_of_nonneg_left hn (pow_nonneg (by linarith [logWeight65_one_le n]) _)
    _ = _ := by rw [pow_add]; dsimp [logWeight65]; ring

end Luce.Section6
