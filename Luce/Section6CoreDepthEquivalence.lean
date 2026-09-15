import Luce.Section6CoreCategoryDefinitions
import Luce.Section6CollisionDepthSums

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- On a core contained in the population, endpoint depth is an exact
bijection onto the integer depth interval, for either supported corner. -/
def coreDepthEquiv {n A B : ℕ} (hA : 1 ≤ A) (hB : B ≤ n) (side : Corner) :
    CollisionCore n A B side ≃ ↥(Finset.Icc A B) where
  toFun v := ⟨cornerDistance side v.val, Finset.mem_Icc.mpr v.property⟩
  invFun m := by
    have hm := Finset.mem_Icc.mp m.property
    cases side with
    | left => exact ⟨⟨m.val-1, by omega⟩, by dsimp [cornerDistance]; omega⟩
    | right => exact ⟨⟨n-m.val, by omega⟩, by dsimp [cornerDistance]; omega⟩
  left_inv v := by
    apply Subtype.ext
    apply Fin.ext
    cases side <;> dsimp [cornerDistance] <;> omega
  right_inv m := by
    apply Subtype.ext
    have hm := Finset.mem_Icc.mp m.property
    cases side <;> dsimp [cornerDistance] <;> omega

theorem category_set_root_eq_tuple_root {n k : ℕ} (side : Corner) (x : Fin (k+1) → Fin n) :
    categorySetRootDepth side (Finset.univ.image x) =
      idealTupleRoot side k (fun j => cornerDistance side (x j)) := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin (k+1) => (x j).val) Finset.univ_nonempty
  have hsup : (Finset.univ.image x).sup (fun v => v.val) = (x i).val := by
    apply le_antisymm
    · apply Finset.sup_le
      intro v hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      exact hmax j hj
    · exact Finset.le_sup (f := fun v : Fin n => v.val) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  cases side with
  | left =>
    dsimp [categorySetRootDepth, idealTupleRoot, cornerDistance]
    rw [hsup]
    apply le_antisymm
    · exact Finset.le_sup' (fun j => (x j).val+1) hi
    · apply Finset.sup'_le
      intro j hj
      exact Nat.add_le_add_right (hmax j hj) 1
  | right =>
    dsimp [categorySetRootDepth, idealTupleRoot, cornerDistance]
    rw [hsup]
    apply le_antisymm
    · apply Finset.le_inf'
      intro j hj
      exact Nat.sub_le_sub_left (hmax j hj) n
    · exact Finset.inf'_le (fun j => n-(x j).val) hi

theorem core_tuple_labels_injective_iff {n A B k : ℕ} (side : Corner)
    (x : Fin (k+1) → CollisionCore n A B side) :
    Function.Injective (fun j => (x j).val) ↔
      Function.Injective (fun j => cornerDistance side (x j).val) := by
  constructor
  · intro hx i j h
    exact hx (cornerDistance_injective67 side h)
  · intro hx i j h
    exact hx (congrArg (cornerDistance side) h)

end Luce.Section6
