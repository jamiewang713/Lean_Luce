import Luce.Section6IdealTraceDefinitions
import Luce.Section5CycleProbability

/-! Literal category counts and exact ideal means for Proposition 6.10.
An interval may depend on n; this includes the thresholds n^a,n^b in the
manuscript. The estimate is uniform in these deterministic restrictions. -/
noncomputable section
open scoped BigOperators
namespace Luce.Section6

inductive CoreRootWindow where
  | all
  | interval (lower upper : ℕ → ℝ)

def CoreRootWindow.Allows : CoreRootWindow → ℕ → ℕ → Prop
  | .all, _, _ => True
  | .interval lower upper, n, m => lower n < (m : ℝ) ∧ (m : ℝ) ≤ upper n

structure CoreCycleCategory where
  side : Corner
  lengthIndex : ℕ
  rootWindow : CoreRootWindow

/-- The actual root is always the largest label. Its left depth is the
maximum left depth, and its right depth is the minimum right depth. -/
def categorySetRootDepth {n : ℕ} (side : Corner) (S : Finset (Fin n)) : ℕ :=
  match side with
  | .left => S.sup (fun v => v.val)+1
  | .right => n-S.sup (fun v => v.val)

def CategoryAdmissible {n : ℕ} (A B : ℕ) (c : CoreCycleCategory)
    (S : Finset (Fin n)) : Prop :=
  (∀ v ∈ S, A ≤ cornerDistance c.side v ∧ cornerDistance c.side v ≤ B) ∧
    c.rootWindow.Allows n (categorySetRootDepth c.side S)

def coreCategoryCount {n : ℕ} (R : Equiv.Perm (Fin n)) (c : CoreCycleCategory) : ℕ := by
  classical
  exact ((Section5.cycleOrbits R c.lengthIndex).filter (fun orb =>
    CategoryAdmissible (idealCoreLower n) (idealCoreUpper n) c orb.toFinset)).card

/-- Exact ideal sums, including the original rotational divisor and all
boundary corrections. No asymptotic intensity replaces these means. -/
def coreCategoryIdealMean (left right : EndpointBehavior) (n : ℕ) (c : CoreCycleCategory) : ℝ :=
  match c.rootWindow with
  | .all => idealTrace c.side (cornerBehavior left right c.side)
      c.lengthIndex (idealCoreLower n) (idealCoreUpper n)
  | .interval lower upper => idealRootTrace c.side (cornerBehavior left right c.side)
      c.lengthIndex (idealCoreLower n) (idealCoreUpper n) (lower n) (upper n)

def CoreCategoriesDisjoint {q : ℕ} (c : Fin q → CoreCycleCategory) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ i j : Fin q, i ≠ j → (c i).side = (c j).side →
    (c i).lengthIndex = (c j).lengthIndex → ∀ m : ℕ,
      ¬ ((c i).rootWindow.Allows n m ∧ (c j).rootWindow.Allows n m)

end Luce.Section6
