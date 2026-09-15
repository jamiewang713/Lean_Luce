import Luce.Section5ShellMarkedEdge
import Luce.Section5LateShellGeometry

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Integrating the marked-edge bound over the source cutoff. Its local
rate and time premises are supplied by shell minima or retained interior rates. -/
theorem late_marked_edge_integral {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S : Finset (Fin n)) {b s : ℝ} (hb : 0 < b) (hbs : 1 ≤ b*s)
    (hrate : ∀ u ∈ S, b ≤ w.rate u) :
    (∫ t in Set.Ioi s,
      ∑ v ∈ Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t),
        ∑ u ∈ S, w.rate u * Real.exp (-w.rate u*t) *
          markedReturnWeight (ghostEntry w ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) * Real.exp (-b*s) := by
  let F := fun t : ℝ =>
    ∑ v ∈ Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t),
      ∑ u ∈ S, w.rate u * Real.exp (-w.rate u*t) *
        markedReturnWeight (ghostEntry w ell old) k v u
  let C : ℝ := (2*ell+1 : ℕ)^(k+2)
  have hm : Measurable F := by
    dsimp [F]
    simp only [Finset.sum_filter]
    apply Finset.measurable_sum
    intro v _
    apply Measurable.ite (measurableSet_ghostWindowByOrder old hinj ell v) _ measurable_const
    exact Finset.measurable_sum _ (fun u _ => by fun_prop)
  have hnonnegF (t : ℝ) : 0 ≤ F t := by
    apply Finset.sum_nonneg
    intro v _
    apply Finset.sum_nonneg
    intro u _
    exact mul_nonneg (mul_nonneg (w.positive u).le (Real.exp_pos _).le)
      (markedReturnWeight_nonneg _ (fun u v => (ghostEntry_mem_Icc w ell old u v).1) k v u)
  have hbound (t : ℝ) (ht : s < t) : F t ≤ C * (b * Real.exp (-b*t)) := by
    apply ghost_marked_edge_bound w ell k old hinj hnonneg S t _ (by positivity)
    intro u hu
    exact exponential_density_le hb (hrate u hu)
      (hbs.trans (mul_le_mul_of_nonneg_left ht.le hb.le))
  have hdom : IntegrableOn (fun t => C * (b * Real.exp (-b*t))) (Set.Ioi s) :=
    (integrableOn_exponential_density_Ioi hb s).const_mul C
  have hint : IntegrableOn F (Set.Ioi s) := by
    apply hdom.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonnegF t)] using hbound t ht
  calc
    _ ≤ ∫ t in Set.Ioi s, C * (b * Real.exp (-b*t)) := by
      apply integral_mono_ae hint hdom
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = _ := by rw [integral_const_mul, integral_exponential_density_Ioi hb]

theorem late_source_shell_marked_integral (w : WeightArray) (n r ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (hs : (terminalShell n r).Nonempty)
    (hfloor : 1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :
    (∫ t in Set.Ioi ((r : ℝ) - Real.sqrt r),
      ∑ v ∈ Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t),
        ∑ u ∈ terminalShell n r, (w n).rate u * Real.exp (-(w n).rate u*t) *
          markedReturnWeight (ghostEntry (w n) ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) *
        Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :=
  late_marked_edge_integral (w n) ell k old hinj hnonneg (terminalShell n r)
    (shellFloor_pos w n r hs) hfloor.le (fun _ hu => shellFloor_le_rate w hs hu)

end Luce
