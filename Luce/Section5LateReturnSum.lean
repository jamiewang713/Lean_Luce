import Luce.Section5LateDensity
import Luce.Section5LateMarkedIntegral

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Exact interchange of finite return sums with the literal late-edge
integral, at a common source cutoff. All integrability is proved. -/
theorem late_return_sum_eq_integral {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S : Finset (Fin n)) (s : ℝ) :
    (∑ v : Fin n, ∑ u ∈ S, lateGhostEntry w ell old hinj u v s *
      markedReturnWeight (ghostEntry w ell old) k v u) =
    ∫ t in Set.Ioi s,
      ∑ v ∈ Finset.univ.filter (fun v => GhostWindowByOrder old hinj ell v t),
        ∑ u ∈ S, w.rate u * Real.exp (-w.rate u*t) *
          markedReturnWeight (ghostEntry w ell old) k v u := by
  let F := fun (v u : Fin n) (t : ℝ) =>
    {t | GhostWindowByOrder old hinj ell v t}.indicator
      (fun t => w.rate u * Real.exp (-w.rate u*t)) t *
        markedReturnWeight (ghostEntry w ell old) k v u
  have hint (v u : Fin n) : IntegrableOn (F v u) (Set.Ioi s) :=
    ((integrableOn_exponential_density_Ioi (w.positive u) s).indicator
      (measurableSet_ghostWindowByOrder old hinj ell v)).mul_const _
  have heq (v u : Fin n) : lateGhostEntry w ell old hinj u v s *
      markedReturnWeight (ghostEntry w ell old) k v u = ∫ t in Set.Ioi s, F v u t := by
    rw [lateGhostEntry_eq_window_integral w ell old hinj hnonneg u v s,
      integral_mul_const]
  simp_rw [heq]
  simp_rw [← integral_finsetSum S (fun u _ => hint _ u)]
  rw [← integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun u _ => hint v u))]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : GhostWindowByOrder old hinj ell v t
  · simp [F, Set.indicator_apply, hv]
  · simp [F, Set.indicator_apply, hv]

/-- The concrete late ghost-return sum inherits the integrated marked-edge
bound. The source-set minimum and cutoff premises remain explicit helpers. -/
theorem late_return_sum_le {n : ℕ} (w : Weights n) (ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S : Finset (Fin n)) {b s : ℝ} (hb : 0 < b) (hbs : 1 ≤ b*s)
    (hrate : ∀ u ∈ S, b ≤ w.rate u) :
    (∑ v : Fin n, ∑ u ∈ S, lateGhostEntry w ell old hinj u v s *
      markedReturnWeight (ghostEntry w ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) * Real.exp (-b*s) := by
  rw [late_return_sum_eq_integral w ell k old hinj hnonneg S s]
  exact late_marked_edge_integral w ell k old hinj hnonneg S hb hbs hrate

end Luce
