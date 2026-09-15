import Luce.Section3CompensatorLimit
import Luce.Section5BulkCylinder
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The analytic cyclic kernel passage

Source: `fixed_points.tex:1052–1075`. The finite product comparison below is
the telescoping argument with every source-rate error explicit. Its product
envelope is integrable on the product space, so L1 profile convergence does
not require pointwise profile convergence or boundedness of the profile.
-/

noncomputable section
open MeasureTheory Filter Set Function
open scoped Topology BigOperators

namespace Luce

/-- The density rho, with source coordinate first and target rank second. -/
def cyclicProfileDensity (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  rateKernel (profileQuantile profileMeasure f y) (f x) /
    profileD profileMeasure f (profileQuantile profileMeasure f y)

def cyclicProfileMeasure (r : ℕ) : Measure (Fin r → ℝ) :=
  Measure.pi (fun _ : Fin r => profileMeasure)

instance (r : ℕ) : IsProbabilityMeasure (cyclicProfileMeasure r) := by
  unfold cyclicProfileMeasure
  infer_instance

def cyclicBulkCube (r : ℕ) (α : ℝ) : Set (Fin r → ℝ) :=
  Set.pi Set.univ (fun _ => Icc (0 : ℝ) α)

def cyclicBulkInterior (r : ℕ) (α : ℝ) : Set (Fin r → ℝ) :=
  Set.pi Set.univ (fun _ => Ioc (0 : ℝ) α)

/-- The signed finite cyclic sum of Lemma 5.2 in the original row n.
Injectivity is global and the race rank and target labels are one-based. -/
def cyclicRaceSum {n r : ℕ} (w : Weights n) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) : ℝ := by
  classical
  exact ∑ i : Fin r ↪ Fin n,
    if ∀ a, ((i a).val : ℝ) + 1 ≤ α * n then
      g (fun a => ((i a).val + 1 : ℝ) / n) *
        (exponentialRace w).real
          {E | ∀ a, raceRank E (i a) = (i (τ a)).val + 1}
    else 0

def cyclicProfileIntegral {r : ℕ} (f : ℝ → ℝ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) : ℝ :=
  ∫ x in cyclicBulkInterior r α,
    g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a)) ∂cyclicProfileMeasure r

/-- The coefficient G includes the signed test function and the product of
reciprocal denominators. Its continuity will be derived from those objects. -/
def cyclicGridKernel {r : ℕ} (n : ℕ) (α : ℝ) (τ : Equiv.Perm (Fin r))
    (G : (Fin r → ℝ) → ℝ) (t f : ℝ → ℝ) (x : Fin r → ℝ) : ℝ := by
  classical
  exact if ∀ a, 0 < x a ∧ profileGridEndpoint n (x a) ≤ α then
    G (fun a => profileGridEndpoint n (x a)) *
      ∏ a, rateKernel (t (profileGridEndpoint n (x (τ a)))) (f (x a))
  else 0

def cyclicLimitKernel {r : ℕ} (α : ℝ) (τ : Equiv.Perm (Fin r))
    (G : (Fin r → ℝ) → ℝ) (t f : ℝ → ℝ) : (Fin r → ℝ) → ℝ :=
  (cyclicBulkInterior r α).indicator (fun x =>
    G x * ∏ a, rateKernel (t (x (τ a))) (f (x a)))

/-- A quantitative finite-product telescoping bound. The base factors need
only the bounds H; each replacement is charged its own error E. -/
lemma abs_prod_sub_prod_le_envelope {ι : Type*} (s : Finset ι)
    (A B H E : ι → ℝ) (hH : ∀ i ∈ s, 0 ≤ H i) (hE : ∀ i ∈ s, 0 ≤ E i)
    (hB : ∀ i ∈ s, |B i| ≤ H i) (hAB : ∀ i ∈ s, |A i - B i| ≤ E i) :
    |(∏ i ∈ s, A i) - ∏ i ∈ s, B i| ≤
      (∏ i ∈ s, (H i + E i)) - ∏ i ∈ s, H i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hH' := fun j hj => hH j (Finset.mem_insert_of_mem hj)
    have hE' := fun j hj => hE j (Finset.mem_insert_of_mem hj)
    have hB' := fun j hj => hB j (Finset.mem_insert_of_mem hj)
    have hAB' := fun j hj => hAB j (Finset.mem_insert_of_mem hj)
    have hpA : |∏ j ∈ s, A j| ≤ ∏ j ∈ s, (H j + E j) := by
      rw [Finset.abs_prod]
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro j hj
      calc
        |A j| = |B j + (A j - B j)| := by congr 1; ring
        _ ≤ |B j| + |A j - B j| := abs_add_le _ _
        _ ≤ H j + E j := add_le_add (hB' j hj) (hAB' j hj)
    have hpE : 0 ≤ (∏ j ∈ s, (H j + E j)) - ∏ j ∈ s, H j :=
      sub_nonneg.mpr (Finset.prod_le_prod hH' (fun j hj => le_add_of_nonneg_right (hE' j hj)))
    have hh := ih hH' hE' hB' hAB'
    have hBi := hB i (Finset.mem_insert_self _ _)
    have hEi := hAB i (Finset.mem_insert_self _ _)
    have hHi := hH i (Finset.mem_insert_self _ _)
    have hEi0 := hE i (Finset.mem_insert_self _ _)
    simp only [Finset.prod_insert hi]
    calc
      |A i * (∏ j ∈ s, A j) - B i * ∏ j ∈ s, B j| =
          |(A i - B i) * (∏ j ∈ s, A j) +
            B i * ((∏ j ∈ s, A j) - ∏ j ∈ s, B j)| := by congr 1; ring
      _ ≤ |A i - B i| * |∏ j ∈ s, A j| +
          |B i| * |(∏ j ∈ s, A j) - ∏ j ∈ s, B j| := by
        simpa only [abs_mul] using abs_add_le
          ((A i - B i) * (∏ j ∈ s, A j))
          (B i * ((∏ j ∈ s, A j) - ∏ j ∈ s, B j))
      _ ≤ E i * (∏ j ∈ s, (H j + E j)) +
          H i * ((∏ j ∈ s, (H j + E j)) - ∏ j ∈ s, H j) :=
        add_le_add (mul_le_mul hEi hpA (abs_nonneg _) hEi0)
          (mul_le_mul hBi hh (abs_nonneg _) hHi)
      _ = (H i + E i) * (∏ j ∈ s, (H j + E j)) - H i * ∏ j ∈ s, H j := by ring

/-- Product-space almost-everywhere statements are lifted coordinatewise. -/
lemma cyclic_ae_coordinates {r : ℕ} {p : ℝ → Prop}
    (hp : ∀ᵐ y ∂profileMeasure, p y) :
    ∀ᵐ x ∂cyclicProfileMeasure r, ∀ a, p (x a) :=
  eventually_all.mpr fun _ => Measure.tendsto_eval_ae_ae.eventually hp

lemma integrable_cyclic_source_product {r : ℕ} {f : ℝ → ℝ}
    (hf : Integrable f profileMeasure) :
    Integrable (fun x : Fin r → ℝ => ∏ a, f (x a)) (cyclicProfileMeasure r) :=
  Integrable.fintype_prod (fun _ => hf)

lemma integral_cyclic_source_product {r : ℕ} (f : ℝ → ℝ) :
    (∫ x : Fin r → ℝ, ∏ a, f (x a) ∂cyclicProfileMeasure r) =
      (∫ y, f y ∂profileMeasure) ^ r := by
  simpa only [Fintype.card_fin, cyclicProfileMeasure] using
    (integral_fintype_prod_eq_pow (ι := Fin r) (μ := profileMeasure) f)

/-- A continuous function on the source cube admits an ambient function
continuous on that cube. No ambient continuity is asserted or needed; this
also covers empty cubes and degenerate endpoint cubes. -/
theorem exists_cyclic_test_extension {r : ℕ} {α : ℝ}
    (g : cyclicBulkCube r α → ℝ) (hg : Continuous g) :
    ∃ G : (Fin r → ℝ) → ℝ, ContinuousOn G (cyclicBulkCube r α) ∧
      ∀ x : cyclicBulkCube r α, G x.val = g x := by
  let G := Function.extend Subtype.val g (fun _ => (0 : ℝ))
  have he (x : cyclicBulkCube r α) : G x.val = g x :=
    Subtype.val_injective.extend_apply g _ x
  refine ⟨G, ?_, he⟩
  rw [continuousOn_iff_continuous_domRestrict]
  convert hg using 1
  funext x
  exact he x

lemma measurable_cyclic_grid_comp {r : ℕ} (n : ℕ) (G : (Fin r → ℝ) → ℝ) :
    Measurable (fun x : Fin r → ℝ => G (fun a => profileGridEndpoint n (x a))) := by
  let q : (Fin r → ℝ) → (Fin r → ℕ) := fun x a => ⌈x a * (n + 1 : ℕ)⌉₊
  have hq : Measurable q := measurable_pi_lambda _ fun a => by
    dsimp only [q]
    have hpa : Measurable (fun x : Fin r → ℝ => x a) := measurable_pi_apply a
    exact (hpa.mul_const ((n + 1 : ℕ) : ℝ)).nat_ceil
  exact (measurable_of_countable (fun u : Fin r → ℕ =>
    G (fun a => (u a : ℝ) / (n + 1 : ℕ)))).comp hq

lemma aestronglyMeasurable_cyclicGridKernel {r : ℕ} (n : ℕ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f profileMeasure) :
    AEStronglyMeasurable (cyclicGridKernel n α τ G t f) (cyclicProfileMeasure r) := by
  have hset : MeasurableSet {x : Fin r → ℝ |
      ∀ a, 0 < x a ∧ profileGridEndpoint n (x a) ≤ α} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    exact (measurableSet_lt measurable_const (measurable_pi_apply a)).inter
      (measurableSet_le ((measurable_profileGridEndpoint n).comp (measurable_pi_apply a))
        measurable_const)
  have hG := (measurable_cyclic_grid_comp n G).aestronglyMeasurable
    (μ := cyclicProfileMeasure r)
  have hp : AEStronglyMeasurable (fun x : Fin r → ℝ =>
      ∏ a, rateKernel (t (profileGridEndpoint n (x (τ a)))) (f (x a)))
      (cyclicProfileMeasure r) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro a _
    have hfa : AEStronglyMeasurable (fun x : Fin r → ℝ => f (x a))
        (cyclicProfileMeasure r) :=
      hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin r => profileMeasure) a)
    have hta := ((measurable_comp_profileGridEndpoint n t).comp
      (measurable_pi_apply (τ a))).aestronglyMeasurable (μ := cyclicProfileMeasure r)
    exact hfa.mul (Real.continuous_exp.comp_aestronglyMeasurable (hta.neg.mul hfa))
  apply ((hG.mul hp).indicator hset).congr
  filter_upwards [] with x
  simp only [cyclicGridKernel, Set.indicator_apply, Set.mem_ofPred_eq, Pi.mul_apply]

lemma abs_cyclicGridKernel_le {r n : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t f : ℝ → ℝ)
    (hB : 0 ≤ B) (hG : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    {x : Fin r → ℝ} (hf : ∀ a, 0 ≤ f (x a)) :
    |cyclicGridKernel n α τ G t f x| ≤ B * ∏ a, f (x a) := by
  classical
  unfold cyclicGridKernel
  split_ifs with hx
  · have hxx : (fun a => profileGridEndpoint n (x a)) ∈ cyclicBulkCube r α :=
      fun a _ => ⟨(profileGridEndpoint_pos n (hx a).1).le, (hx a).2⟩
    rw [abs_mul, Finset.abs_prod]
    apply mul_le_mul (hG _ hxx) _ (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) hB
    apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    intro a _
    rw [abs_of_nonneg (rateKernel_nonneg (hf a))]
    exact rateKernel_le (ht _ (hxx (τ a) (mem_univ _))) (hf a)
  · simpa only [abs_zero] using mul_nonneg hB (Finset.prod_nonneg (fun a _ => hf a))

lemma integrable_cyclicGridKernel {r n : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ)
    (hB : 0 ≤ B) (hG : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    {f : ℝ → ℝ} (hf : Integrable f profileMeasure)
    (hf0 : ∀ᵐ y ∂profileMeasure, 0 ≤ f y) :
    Integrable (cyclicGridKernel n α τ G t f) (cyclicProfileMeasure r) := by
  apply ((integrable_cyclic_source_product hf).const_mul B).mono'
    (aestronglyMeasurable_cyclicGridKernel n α τ G t hf.1)
  filter_upwards [cyclic_ae_coordinates (r := r) hf0] with x hx
  exact abs_cyclicGridKernel_le τ G t f hB hG ht hx

lemma abs_cyclicGridKernel_sub_le {r n : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t f h : ℝ → ℝ)
    (hB : 0 ≤ B) (hG : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    {x : Fin r → ℝ} (hf : ∀ a, 0 ≤ f (x a)) (hh : ∀ a, 0 ≤ h (x a)) :
    |cyclicGridKernel n α τ G t h x - cyclicGridKernel n α τ G t f x| ≤
      B * ((∏ a, (f (x a) + |h (x a) - f (x a)|)) - ∏ a, f (x a)) := by
  classical
  have hnonneg : 0 ≤ (∏ a, (f (x a) + |h (x a) - f (x a)|)) - ∏ a, f (x a) :=
    sub_nonneg.mpr (Finset.prod_le_prod (fun a _ => hf a)
      (fun _ _ => le_add_of_nonneg_right (abs_nonneg _)))
  unfold cyclicGridKernel
  split_ifs with hx
  · have hxx : (fun a => profileGridEndpoint n (x a)) ∈ cyclicBulkCube r α :=
      fun a _ => ⟨(profileGridEndpoint_pos n (hx a).1).le, (hx a).2⟩
    rw [← mul_sub, abs_mul]
    apply mul_le_mul (hG _ hxx) _ (abs_nonneg _) hB
    apply abs_prod_sub_prod_le_envelope
    · exact fun a _ => hf a
    · exact fun _ _ => abs_nonneg _
    · intro a _
      rw [abs_of_nonneg (rateKernel_nonneg (hf a))]
      exact rateKernel_le (ht _ (hxx (τ a) (mem_univ _))) (hf a)
    · intro a _
      exact abs_rateKernel_sub_le (ht _ (hxx (τ a) (mem_univ _))) (hh a) (hf a)
  · simpa only [sub_self, abs_zero] using mul_nonneg hB hnonneg

/-- Exact integrated L1 product error; finiteness of both products and of
the error envelope is established before subtracting their integrals. -/
theorem integral_cyclicGridKernel_sub_le {r n : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ)
    (hB : 0 ≤ B) (hG : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    {f h : ℝ → ℝ} (hf : Integrable f profileMeasure) (hh : Integrable h profileMeasure)
    (hf0 : ∀ᵐ y ∂profileMeasure, 0 ≤ f y) (hh0 : ∀ᵐ y ∂profileMeasure, 0 ≤ h y) :
    |(∫ x, cyclicGridKernel n α τ G t h x ∂cyclicProfileMeasure r) -
        ∫ x, cyclicGridKernel n α τ G t f x ∂cyclicProfileMeasure r| ≤
      B * (((∫ y, f y ∂profileMeasure) +
        ∫ y, |h y - f y| ∂profileMeasure) ^ r - (∫ y, f y ∂profileMeasure) ^ r) := by
  have he : Integrable (fun y => |h y - f y|) profileMeasure := (hh.sub hf).abs
  have hp : Integrable (fun x : Fin r → ℝ => ∏ a, (f (x a) + |h (x a) - f (x a)|))
      (cyclicProfileMeasure r) := by
    simpa only [Pi.add_apply] using integrable_cyclic_source_product (r := r) (hf.add he)
  have hq := integrable_cyclic_source_product (r := r) hf
  have henv : Integrable (fun x : Fin r → ℝ =>
      B * ((∏ a, (f (x a) + |h (x a) - f (x a)|)) - ∏ a, f (x a)))
      (cyclicProfileMeasure r) := (hp.sub hq).const_mul B
  rw [← integral_sub (integrable_cyclicGridKernel τ G t hB hG ht hh hh0)
    (integrable_cyclicGridKernel τ G t hB hG ht hf hf0)]
  calc
    _ ≤ ∫ x : Fin r → ℝ, B *
        ((∏ a, (f (x a) + |h (x a) - f (x a)|)) - ∏ a, f (x a))
        ∂cyclicProfileMeasure r := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le henv
      filter_upwards [cyclic_ae_coordinates (r := r) hf0,
        cyclic_ae_coordinates (r := r) hh0] with x hfx hhx
      exact abs_cyclicGridKernel_sub_le τ G t f h hB hG ht hfx hhx
    _ = _ := by
      rw [integral_const_mul, integral_sub hp hq,
        integral_cyclic_source_product (r := r) (fun y => f y + |h y - f y|),
        integral_cyclic_source_product f, integral_add hf he]

/-- The source's L1 hypothesis alone gives the product replacement, uniformly
over the cellwise rank times. No boundedness of f or pointwise convergence
of the step profiles is assumed. -/
theorem ProfileLimit.tendsto_cyclic_grid_profile_replacement {w : WeightArray}
    {f : ℝ → ℝ} (hf : ProfileLimit w f) {r : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ)
    (hB : 0 ≤ B) (hG : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) :
    Tendsto (fun n =>
      (∫ x, cyclicGridKernel n α τ G t (stepProfile w (n + 1)) x ∂cyclicProfileMeasure r) -
        ∫ x, cyclicGridKernel n α τ G t f x ∂cyclicProfileMeasure r) atTop (𝓝 0) := by
  have herr := hf.tendsto_integral_abs_sub.comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero_norm (fun n => integral_cyclicGridKernel_sub_le τ G t hB hG ht
    hf.integrable (integrable_stepProfile w (n + 1)) hf.ae_nonneg
    (Eventually.of_forall (stepProfile_nonneg w (n + 1))))
  have hc : Tendsto (fun _ : ℕ => ∫ y, f y ∂profileMeasure) atTop
      (𝓝 (∫ y, f y ∂profileMeasure)) := tendsto_const_nhds
  simpa only [Function.comp_apply, add_zero, sub_self, mul_zero] using
    (((hc.add herr).pow r).sub (hc.pow r)).const_mul B

lemma tendsto_cyclicGridKernel {r : ℕ} {α : ℝ} (τ : Equiv.Perm (Fin r))
    {G : (Fin r → ℝ) → ℝ} {t f : ℝ → ℝ}
    (hG : ContinuousOn G (cyclicBulkCube r α))
    (ht : ContinuousOn t (Icc (0 : ℝ) α)) {x : Fin r → ℝ}
    (hx0 : ∀ a, 0 < x a) (hxa : ∀ a, x a ≠ α) :
    Tendsto (fun n => cyclicGridKernel n α τ G t f x) atTop
      (𝓝 (cyclicLimitKernel α τ G t f x)) := by
  classical
  have hq (a : Fin r) := tendsto_profileGridEndpoint (hx0 a).le
  by_cases hxα : ∀ a, x a < α
  · have hcube : cyclicBulkCube r α ∈ 𝓝 x :=
      set_pi_mem_nhds finite_univ (fun a _ => Icc_mem_nhds (hx0 a) (hxα a))
    have hGlim := (hG.continuousAt hcube).tendsto.comp
      (tendsto_pi_nhds.mpr hq)
    have hprod : Tendsto (fun n => ∏ a,
        rateKernel (t (profileGridEndpoint n (x (τ a)))) (f (x a))) atTop
        (𝓝 (∏ a, rateKernel (t (x (τ a))) (f (x a)))) := by
      apply tendsto_finsetProd
      intro a _
      have hta := (ht.continuousAt (Icc_mem_nhds (hx0 (τ a)) (hxα (τ a)))).tendsto
      have hr : Continuous (fun z : ℝ => rateKernel z (f (x a))) := by
        unfold rateKernel survivalKernel
        fun_prop
      exact (hr.tendsto _).comp (hta.comp (hq (τ a)))
    have hevent : ∀ᶠ n in atTop, ∀ a, profileGridEndpoint n (x a) ≤ α :=
      eventually_all.mpr (fun a => ((hq a).eventually (gt_mem_nhds (hxα a))).mono
        (fun _ hy => hy.le))
    have hxmem : x ∈ cyclicBulkInterior r α := fun a _ => ⟨hx0 a, (hxα a).le⟩
    simp only [cyclicLimitKernel, Set.indicator_of_mem hxmem]
    apply (hGlim.mul hprod).congr'
    filter_upwards [hevent] with n hn
    rw [cyclicGridKernel, if_pos (fun a => ⟨hx0 a, hn a⟩)]
    rfl
  · obtain ⟨a, ha⟩ := not_forall.mp hxα
    have hgt : α < x a := lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm (hxa a))
    have hnot (n : ℕ) : ¬∀ b, 0 < x b ∧ profileGridEndpoint n (x b) ≤ α := by
      intro h
      exact not_le_of_gt (hgt.trans_le (profileGridEndpoint_ge n (x a))) (h a).2
    have hxnot : x ∉ cyclicBulkInterior r α :=
      fun h => not_le_of_gt hgt (h a (mem_univ a)).2
    simp only [cyclicGridKernel, hnot, if_false, cyclicLimitKernel,
      Set.indicator_of_notMem hxnot]
    exact tendsto_const_nhds

lemma ae_tendsto_cyclicGridKernel {r : ℕ} {α : ℝ} (τ : Equiv.Perm (Fin r))
    {G : (Fin r → ℝ) → ℝ} {t f : ℝ → ℝ}
    (hG : ContinuousOn G (cyclicBulkCube r α))
    (ht : ContinuousOn t (Icc (0 : ℝ) α)) :
    ∀ᵐ x ∂cyclicProfileMeasure r,
      Tendsto (fun n => cyclicGridKernel n α τ G t f x) atTop
        (𝓝 (cyclicLimitKernel α τ G t f x)) := by
  have : NullSingletonClass profileMeasure := by unfold profileMeasure; infer_instance
  have hx0 : ∀ᵐ y ∂profileMeasure, 0 < y :=
    (ae_restrict_mem measurableSet_Ioo).mono (fun _ h => h.1)
  filter_upwards [cyclic_ae_coordinates (r := r) hx0,
    cyclic_ae_coordinates (r := r) (profileMeasure.ae_ne α)] with x hx hxa
  exact tendsto_cyclicGridKernel τ hG ht hx hxa

lemma integrable_cyclicLimitKernel {r : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) {G : (Fin r → ℝ) → ℝ} {t f : ℝ → ℝ}
    (hB : 0 ≤ B) (hG : ContinuousOn G (cyclicBulkCube r α))
    (hGB : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht0 : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    (hf : Integrable f profileMeasure) (hf0 : ∀ᵐ y ∂profileMeasure, 0 ≤ f y) :
    Integrable (cyclicLimitKernel α τ G t f) (cyclicProfileMeasure r) := by
  have hlim := ae_tendsto_cyclicGridKernel (f := f) τ hG ht
  apply ((integrable_cyclic_source_product hf).const_mul B).mono'
  · exact aestronglyMeasurable_of_tendsto_ae _
      (fun n => aestronglyMeasurable_cyclicGridKernel n α τ G t hf.1) hlim
  · filter_upwards [cyclic_ae_coordinates (r := r) hf0, hlim] with x hx hxl
    exact le_of_tendsto hxl.norm (Eventually.of_forall (fun n =>
      abs_cyclicGridKernel_le τ G t f hB hGB ht0 hx))

/-- Dominated convergence performs the cell-endpoint passage for the fixed
limiting profile, using the integrable product of its source rates. -/
theorem tendsto_integral_cyclicGridKernel {r : ℕ} {α B : ℝ}
    (τ : Equiv.Perm (Fin r)) {G : (Fin r → ℝ) → ℝ} {t f : ℝ → ℝ}
    (hB : 0 ≤ B) (hG : ContinuousOn G (cyclicBulkCube r α))
    (hGB : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B)
    (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht0 : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y)
    (hf : Integrable f profileMeasure) (hf0 : ∀ᵐ y ∂profileMeasure, 0 ≤ f y) :
    Tendsto (fun n => ∫ x, cyclicGridKernel n α τ G t f x ∂cyclicProfileMeasure r)
      atTop (𝓝 (∫ x, cyclicLimitKernel α τ G t f x ∂cyclicProfileMeasure r)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : Fin r → ℝ => B * ∏ a, f (x a))
    (fun n => aestronglyMeasurable_cyclicGridKernel n α τ G t hf.1)
    ((integrable_cyclic_source_product hf).const_mul B)
  · intro n
    filter_upwards [cyclic_ae_coordinates (r := r) hf0] with x hx
    exact abs_cyclicGridKernel_le τ G t f hB hGB ht0 hx
  · exact ae_tendsto_cyclicGridKernel τ hG ht

/-- The complete analytic step-profile integral passage, with a signed
coefficient continuous only on the source cube. -/
theorem ProfileLimit.tendsto_integral_cyclic_stepKernel {w : WeightArray}
    {f : ℝ → ℝ} (hf : ProfileLimit w f) {r : ℕ} {α : ℝ}
    (τ : Equiv.Perm (Fin r)) {G : (Fin r → ℝ) → ℝ} {t : ℝ → ℝ}
    (hG : ContinuousOn G (cyclicBulkCube r α))
    (ht : ContinuousOn t (Icc (0 : ℝ) α))
    (ht0 : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ t y) :
    Tendsto (fun n => ∫ x, cyclicGridKernel n α τ G t (stepProfile w (n + 1)) x
      ∂cyclicProfileMeasure r) atTop
      (𝓝 (∫ x, cyclicLimitKernel α τ G t f x ∂cyclicProfileMeasure r)) := by
  have hcompact : IsCompact (cyclicBulkCube r α) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hG
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hGB : ∀ x ∈ cyclicBulkCube r α, |G x| ≤ B :=
    fun x hx => (hC x hx).trans (le_max_left _ _)
  have hreplace := hf.tendsto_cyclic_grid_profile_replacement τ G t hB hGB ht0
  have hfixed := tendsto_integral_cyclicGridKernel τ hB hG hGB ht ht0 hf.integrable hf.ae_nonneg
  simpa only [zero_add, sub_add_cancel] using hreplace.add hfixed

/-- Incorporate the target-rank denominators in the signed continuous
coefficient; each source coordinate occurs exactly once in the numerator. -/
def cyclicDensityCoefficient {r : ℕ} (f : ℝ → ℝ) (τ : Equiv.Perm (Fin r))
    (g : (Fin r → ℝ) → ℝ) (x : Fin r → ℝ) : ℝ :=
  g x * ∏ a, (profileD profileMeasure f (profileQuantile profileMeasure f (x (τ a))))⁻¹

lemma continuousOn_cyclicDensityCoefficient {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {r : ℕ} {α : ℝ} (hα : α < 1)
    (τ : Equiv.Perm (Fin r)) {g : (Fin r → ℝ) → ℝ}
    (hg : ContinuousOn g (cyclicBulkCube r α)) :
    ContinuousOn (cyclicDensityCoefficient f τ g) (cyclicBulkCube r α) := by
  have hc : ContinuousOn (fun y => (profileD profileMeasure f
      (profileQuantile profileMeasure f y))⁻¹) (Icc (0 : ℝ) α) := by
    simpa only [one_div] using continuousOn_compensator_coefficient hf hα
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) α))
  apply hg.mul
  apply continuousOn_finsetProd
  intro a _
  exact hc.comp (continuous_apply (τ a)).continuousOn (fun x hx => hx (τ a) (mem_univ _))

lemma cyclicLimitKernel_density_eq {r : ℕ} (f : ℝ → ℝ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicLimitKernel α τ (cyclicDensityCoefficient f τ g)
      (profileQuantile profileMeasure f) f =
      (cyclicBulkInterior r α).indicator
        (fun x => g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a))) := by
  unfold cyclicLimitKernel
  apply Set.indicator_congr
  intro x _
  simp only [cyclicDensityCoefficient, cyclicProfileDensity, div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  ring

lemma cyclicProfileMeasure_restrict_bulk {r : ℕ} {α : ℝ} (hα : α < 1) :
    (cyclicProfileMeasure r).restrict (cyclicBulkInterior r α) =
      volume.restrict (cyclicBulkInterior r α) := by
  unfold cyclicProfileMeasure cyclicBulkInterior
  change (Measure.pi (fun _ : Fin r => profileMeasure)).restrict _ =
    (Measure.pi (fun _ : Fin r => (volume : Measure ℝ))).restrict _
  rw [Measure.restrict_pi_pi, Measure.restrict_pi_pi]
  congr 1
  funext a
  unfold profileMeasure
  exact Measure.restrict_restrict_of_subset
    (show Ioc (0 : ℝ) α ⊆ Ioo (0 : ℝ) 1 from fun _ hx => ⟨hx.1, hx.2.trans_lt hα⟩)

/-- The product profile measure and half-open cube recover exactly the
paper's Lebesgue integral on the closed cube, including its endpoints. -/
theorem cyclicProfileIntegral_eq_volume {r : ℕ} (f : ℝ → ℝ) {α : ℝ} (hα : α < 1)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicProfileIntegral f α τ g =
      ∫ x in cyclicBulkCube r α, g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a)) := by
  unfold cyclicProfileIntegral
  rw [cyclicProfileMeasure_restrict_bulk hα]
  apply setIntegral_congr_set
  exact Measure.pi_Ioc_ae_eq_pi_Icc

theorem cyclicRaceSum_of_nonpos {n r : ℕ} (w : Weights n) {α : ℝ}
    (hα : α ≤ 0) (hr : 0 < r) (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicRaceSum w α τ g = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply if_neg
  intro hi
  have hai := hi (⟨0, hr⟩ : Fin r)
  have hmul := mul_nonpos_of_nonpos_of_nonneg hα (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hlabel : (0 : ℝ) ≤ (i ⟨0, hr⟩).val := Nat.cast_nonneg _
  linarith

theorem cyclicProfileIntegral_of_nonpos {r : ℕ} (f : ℝ → ℝ) {α : ℝ}
    (hα : α ≤ 0) (hr : 0 < r) (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicProfileIntegral f α τ g = 0 := by
  have hempty : cyclicBulkInterior r α = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := hx (⟨0, hr⟩ : Fin r) (mem_univ _)
    exact (not_lt_of_ge hα) (h.1.trans_le h.2)
  simp [cyclicProfileIntegral, hempty]

def cyclicProfileCell {r : ℕ} (n : ℕ) (i : Fin r → Fin (n + 1)) : Set (Fin r → ℝ) :=
  Set.pi Set.univ (fun a => Ioc ((i a).val / (n + 1 : ℕ) : ℝ)
    (((i a).val + 1 : ℝ) / (n + 1 : ℕ)))

lemma measurableSet_cyclicProfileCell {r : ℕ} (n : ℕ) (i : Fin r → Fin (n + 1)) :
    MeasurableSet (cyclicProfileCell n i) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

lemma cyclicProfileCell_real_measure {r : ℕ} (n : ℕ) (i : Fin r → Fin (n + 1)) :
    (cyclicProfileMeasure r).real (cyclicProfileCell n i) = 1 / (n + 1 : ℕ) ^ r := by
  unfold cyclicProfileMeasure cyclicProfileCell
  rw [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  change (∏ a : Fin r, profileMeasure.real
    (Ioc ((i a).val / (n + 1 : ℕ) : ℝ) (((i a).val + 1 : ℝ) / (n + 1 : ℕ)))) = _
  simp only [section3_cell_real_measure, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, one_div, inv_pow]

lemma cyclicProfileCell_unique {r : ℕ} {n : ℕ} {x : Fin r → ℝ}
    {i j : Fin r → Fin (n + 1)} (hi : x ∈ cyclicProfileCell n i)
    (hj : x ∈ cyclicProfileCell n j) : i = j := by
  funext a
  apply Fin.ext
  have he := (profileGridEndpoint_of_mem_cell n (i a) (hi a (mem_univ _))).symm.trans
    (profileGridEndpoint_of_mem_cell n (j a) (hj a (mem_univ _)))
  have hn : (n + 1 : ℕ) ≠ (0 : ℝ) := by positivity
  have hh := (div_left_inj' hn).mp he
  exact_mod_cast (add_right_cancel hh)

def cyclicKernelGridSum {n r : ℕ} (w : Weights n) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ) : ℝ := by
  classical
  exact (∑ i : Fin r → Fin n,
    if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
      G (fun a => ((i a).val + 1 : ℝ) / n) *
        ∏ a, rateKernel (t (((i (τ a)).val + 1 : ℝ) / n)) (w.rate (i a))
    else 0) / (n : ℝ) ^ r

/-- The exact multivariate cell identity: every box has mass n^(-r), and
the terminal fractional box is included precisely by its right endpoint. -/
theorem integral_cyclicGridKernel_step (w : WeightArray) {r : ℕ} (n : ℕ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (G : (Fin r → ℝ) → ℝ) (t : ℝ → ℝ) :
    (∫ x, cyclicGridKernel n α τ G t (stepProfile w (n + 1)) x ∂cyclicProfileMeasure r) =
      cyclicKernelGridSum (w (n + 1)) α τ G t := by
  classical
  let b : (Fin r → Fin (n + 1)) → ℝ := fun i =>
    if ∀ a, ((i a).val + 1 : ℝ) / (n + 1 : ℕ) ≤ α then
      G (fun a => ((i a).val + 1 : ℝ) / (n + 1 : ℕ)) *
        ∏ a, rateKernel (t (((i (τ a)).val + 1 : ℝ) / (n + 1 : ℕ))) ((w (n + 1)).rate (i a))
    else 0
  let H : (Fin r → Fin (n + 1)) → (Fin r → ℝ) → ℝ := fun i =>
    (cyclicProfileCell n i).indicator (fun _ => b i)
  have heq : cyclicGridKernel n α τ G t (stepProfile w (n + 1)) =ᵐ[cyclicProfileMeasure r]
      (fun x => ∑ i, H i x) := by
    have hbase : ∀ᵐ y ∂profileMeasure, y ∈ Ioo (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Ioo
    filter_upwards [cyclic_ae_coordinates (r := r) hbase] with x hx
    choose i hi using (fun a => exists_profile_cell (Nat.succ_pos n) ⟨(hx a).1, (hx a).2.le⟩)
    have hxi : x ∈ cyclicProfileCell n i := fun a _ => hi a
    have hqi (a : Fin r) := profileGridEndpoint_of_mem_cell n (i a) (hi a)
    have hfi (a : Fin r) := stepProfile_eq_of_mem_Ioc w (n + 1) (i a) (hi a)
    have hx0 : ∀ a, 0 < x a := fun a => (hx a).1
    rw [Finset.sum_eq_single i]
    · simp only [H, Set.indicator_of_mem hxi, cyclicGridKernel, hx0, true_and, hqi, hfi, b]
    · intro j _ hji
      exact Set.indicator_of_notMem (fun hj => hji (cyclicProfileCell_unique hj hxi)) _
    · simp
  rw [integral_congr_ae heq, integral_finsetSum]
  · change (∑ i : Fin r → Fin (n + 1), ∫ x, H i x ∂cyclicProfileMeasure r) =
      (∑ i, b i) / (n + 1 : ℕ) ^ r
    simp only [H, integral_indicator_const _ (measurableSet_cyclicProfileCell n _),
      cyclicProfileCell_real_measure, smul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  · intro i _
    exact (integrable_const (b i)).indicator (measurableSet_cyclicProfileCell n i)

/-- The finite-row numerator uses its actual source rate, never a sampled
value of the limiting profile. This is the kernel in source 1040–1045. -/
def finiteCyclicDensity {n : ℕ} (w : Weights n) (f : ℝ → ℝ) (i j : Fin n) : ℝ :=
  rateKernel (profileQuantile profileMeasure f (((j.val : ℝ) + 1) / n)) (w.rate i) /
    profileD profileMeasure f (profileQuantile profileMeasure f (((j.val : ℝ) + 1) / n))

def cyclicDeterministicSum {n r : ℕ} (w : Weights n) (f : ℝ → ℝ) (α : ℝ)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) : ℝ := by
  classical
  exact (∑ i : Fin r → Fin n,
    if ∀ a, ((i a).val + 1 : ℝ) / n ≤ α then
      g (fun a => ((i a).val + 1 : ℝ) / n) * ∏ a, finiteCyclicDensity w f (i a) (i (τ a))
    else 0) / (n : ℝ) ^ r

lemma cyclicDeterministicSum_eq_kernelGridSum {n r : ℕ} (w : Weights n)
    (f : ℝ → ℝ) (α : ℝ) (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ) :
    cyclicDeterministicSum w f α τ g =
      cyclicKernelGridSum w α τ (cyclicDensityCoefficient f τ g) (profileQuantile profileMeasure f) := by
  classical
  unfold cyclicDeterministicSum cyclicKernelGridSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · simp only [finiteCyclicDensity, cyclicDensityCoefficient, div_eq_mul_inv,
      Finset.prod_mul_distrib]
    ring
  · rfl

/-- The complete deterministic cyclic kernel limit in source 1065–1075.
The tuple sum here includes repeated coordinates; the subsequent finite-sum
reduction controls their removal along with nearby coordinates. -/
theorem ProfileLimit.cyclic_deterministic_limit {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {r : ℕ} {α : ℝ} (hα : α < 1)
    (τ : Equiv.Perm (Fin r)) {g : (Fin r → ℝ) → ℝ}
    (hg : ContinuousOn g (cyclicBulkCube r α)) :
    Tendsto (fun n => cyclicDeterministicSum (w (n + 1)) f α τ g) atTop
      (𝓝 (cyclicProfileIntegral f α τ g)) := by
  have hq : ContinuousOn (profileQuantile profileMeasure f) (Icc (0 : ℝ) α) :=
    (continuousOn_profileQuantile hf.integrable hf.ae_pos).mono
      (fun _ hx => ⟨hx.1, hx.2.trans_lt hα⟩)
  have hq0 : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ profileQuantile profileMeasure f y :=
    fun _ hy => profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hy.1, hy.2.trans_lt hα⟩
  have h := hf.tendsto_integral_cyclic_stepKernel τ
    (continuousOn_cyclicDensityCoefficient hf hα τ hg) hq hq0
  have hmeas : MeasurableSet (cyclicBulkInterior r α) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  simpa only [integral_cyclicGridKernel_step, ← cyclicDeterministicSum_eq_kernelGridSum,
    cyclicLimitKernel_density_eq, integral_indicator hmeas,
    cyclicProfileIntegral] using h

/-- The limiting cyclic integral is finite under the original profile
hypothesis and signed test-function assumption. -/
theorem ProfileLimit.integrable_cyclic_density {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {r : ℕ} {α : ℝ} (hα : α < 1)
    (τ : Equiv.Perm (Fin r)) {g : (Fin r → ℝ) → ℝ}
    (hg : ContinuousOn g (cyclicBulkCube r α)) :
    IntegrableOn (fun x => g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a)))
      (cyclicBulkCube r α) := by
  have hG := continuousOn_cyclicDensityCoefficient hf hα τ hg
  have hcompact : IsCompact (cyclicBulkCube r α) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hG
  have hGB : ∀ x ∈ cyclicBulkCube r α, |cyclicDensityCoefficient f τ g x| ≤ max C 0 :=
    fun x hx => (hC x hx).trans (le_max_left _ _)
  have hq : ContinuousOn (profileQuantile profileMeasure f) (Icc (0 : ℝ) α) :=
    (continuousOn_profileQuantile hf.integrable hf.ae_pos).mono
      (fun _ hx => ⟨hx.1, hx.2.trans_lt hα⟩)
  have hq0 : ∀ y ∈ Icc (0 : ℝ) α, 0 ≤ profileQuantile profileMeasure f y :=
    fun _ hy => profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hy.1, hy.2.trans_lt hα⟩
  have h := integrable_cyclicLimitKernel τ (le_max_right C 0) hG hGB hq hq0
    hf.integrable hf.ae_nonneg
  have hmeas : MeasurableSet (cyclicBulkInterior r α) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  rw [cyclicLimitKernel_density_eq, integrable_indicator_iff hmeas] at h
  unfold IntegrableOn at h
  rw [cyclicProfileMeasure_restrict_bulk hα] at h
  change IntegrableOn (fun x => g x * ∏ a, cyclicProfileDensity f (x a) (x (τ a)))
    (cyclicBulkInterior r α) volume at h
  exact (integrableOn_congr_set_ae Measure.pi_Ioc_ae_eq_pi_Icc).mp h

end Luce
