import Luce.Section6ContinuousTraceBounds
import Mathlib.Order.SuccPred.IntervalSucc

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce.Section6

def logCell68 (m : ℕ) : Set ℝ := Ioc (Real.log (m : ℝ)) (Real.log ((m+1 : ℕ) : ℝ))
def logCellWidth68 (m : ℕ) : ℝ := Real.log ((m+1 : ℕ) : ℝ)-Real.log (m : ℝ)

theorem monotone_nat_log68 : Monotone (fun m : ℕ => Real.log (m : ℝ)) := by
  intro m n h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa only [Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

theorem logCell68_disjoint : Pairwise (fun m n : ℕ => Disjoint (logCell68 m) (logCell68 n)) :=
  monotone_nat_log68.pairwise_disjoint_on_Ioc_succ

theorem logCell68_union (A B : ℕ) :
    (⋃ m : ↥(Finset.Icc A B), logCell68 m.val) =
      Ioc (Real.log (A : ℝ)) (Real.log ((B+1 : ℕ) : ℝ)) := by
  have h := monotone_nat_log68.biUnion_Ico_Ioc_map_succ A (B+1)
  change (⋃ m ∈ Ico A (B+1), logCell68 m) = _ at h
  simpa only [logCell68, Set.iUnion_subtype, Set.mem_Ico, Finset.mem_Icc,
    Nat.lt_succ_iff, Nat.succ_eq_add_one] using h

theorem logCellWidth68_pos {m : ℕ} (hm : 0 < m) : 0 < logCellWidth68 m := by
  unfold logCellWidth68
  apply sub_pos.mpr
  exact Real.log_lt_log (by exact_mod_cast hm) (by exact_mod_cast Nat.lt_succ_self m)

theorem logCellWidth68_bounds {m : ℕ} (hm : 0 < m) :
    1/((m : ℝ)+1) ≤ logCellWidth68 m ∧ logCellWidth68 m ≤ 1/(m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmp : 0 < (m : ℝ)+1 := by positivity
  have hr : 0 < ((m : ℝ)+1)/(m : ℝ) := div_pos hmp hmR
  have he : logCellWidth68 m = Real.log (((m : ℝ)+1)/(m : ℝ)) := by
    rw [Real.log_div hmp.ne' hmR.ne']
    simp only [logCellWidth68, Nat.cast_add, Nat.cast_one]
  rw [he]
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hr
    have hi : 1-(((m : ℝ)+1)/(m : ℝ))⁻¹ = 1/((m : ℝ)+1) := by field_simp; ring
    rwa [hi] at h
  · have h := Real.log_le_sub_one_of_pos hr
    have hi : ((m : ℝ)+1)/(m : ℝ)-1 = 1/(m : ℝ) := by field_simp; ring
    rwa [hi] at h

theorem logCell68_offset {A m : ℕ} (hA : 1 ≤ A) (hAm : A ≤ m) {x : ℝ} (hx : x ∈ logCell68 m) :
    |x-Real.log (m : ℝ)| ≤ 1/(A : ℝ) := by
  have hm : 0 < m := lt_of_lt_of_le (by omega : 0 < A) hAm
  rw [abs_of_pos (sub_pos.mpr hx.1)]
  calc
    x-Real.log (m : ℝ) ≤ logCellWidth68 m := sub_le_sub_right hx.2 _
    _ ≤ 1/(m : ℝ) := (logCellWidth68_bounds hm).2
    _ ≤ 1/(A : ℝ) := one_div_le_one_div_of_le (by exact_mod_cast (show 0 < A by omega))
      (by exact_mod_cast hAm)

def logCellCube68 {A B k : ℕ} (a : IdealDepthTuple A B k) : Set (Fin (k+1) → ℝ) :=
  Set.pi Set.univ (fun j => logCell68 (a j).val)

theorem logCellCube68_measurable {A B k : ℕ} (a : IdealDepthTuple A B k) :
    MeasurableSet (logCellCube68 a) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem logCellCube68_union (A B k : ℕ) :
    (⋃ a : IdealDepthTuple A B k, logCellCube68 a) =
      Set.pi Set.univ (fun _ : Fin (k+1) => Ioc (Real.log (A : ℝ)) (Real.log ((B+1 : ℕ) : ℝ))) := by
  unfold logCellCube68
  rw [Set.iUnion_univ_pi (fun (_ : Fin (k+1)) (m : ↥(Finset.Icc A B)) => logCell68 m.val)]
  simp_rw [logCell68_union]

theorem logCellCube68_disjoint (A B k : ℕ) :
    Pairwise (fun a b : IdealDepthTuple A B k => Disjoint (logCellCube68 a) (logCellCube68 b)) := by
  intro a b hab
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
  apply Set.disjoint_univ_pi.mpr
  exact ⟨j, logCell68_disjoint (fun h => hj (Subtype.ext h))⟩

theorem logCellCube68_volume {A B k : ℕ} (hA : 1 ≤ A) (a : IdealDepthTuple A B k) :
    volume.real (logCellCube68 a) = ∏ j, logCellWidth68 (a j).val := by
  unfold logCellCube68
  rw [measureReal_def, volume_pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  change volume.real (logCell68 (a j).val) = logCellWidth68 (a j).val
  unfold logCell68 logCellWidth68
  rw [Real.volume_real_Ioc_of_le (monotone_nat_log68 (Nat.le_succ _))]

end Luce.Section6
