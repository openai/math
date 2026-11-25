import OAI.Optimization.LinearProgramming.PriceGame.ChargingTransferScores
import OAI.Optimization.LinearProgramming.PriceGame.StatesReachable

/-! # The same absolute expert on each possible state

Consume copy tags from the parent towards the destination. This convention makes
peeling off the first tag agree definitionally with moving to the next depth.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open States.Mass

/-- Depth reached by following `count` copies from `level`. -/
def destination : ℕ → ℕ → ℕ
  | 0, level => level
  | count+1, level => destination count (level+1)

@[simp] theorem destination_eq (count level : ℕ) : destination count level = level + count := by
  induction count generalizing level with
  | zero => rfl
  | succ count ih => rw [destination, ih]; omega

/-- The absolute vertex obtained by following the stored copy signs. -/
def absoluteVertex {N : ℕ} : (count level : ℕ) → Descendant (Vertex N level) count → Vertex N (destination count level)
  | 0, _, v => v.1
  | count+1, level, v => absoluteVertex count (level+1) (splitDescendant v)

@[simp] theorem absoluteVertex_join {N : ℕ} (count level : ℕ) (v : Descendant (Vertex N (level+1)) count) :
    absoluteVertex (count+1) level (joinDescendant v) = absoluteVertex count (level+1) v := by
  exact congrArg (absoluteVertex count (level+1)) (split_joinDescendant (V := Vertex N level) v)

/-- Resolve an inherited or future pivot descriptor in the public history. -/
def absolutePivot {N level : ℕ} (count : ℕ) (current : Pivot N level) :
    PivotChoice (Vertex N level) count → Pivot N (destination count level)
  | none => current.map fun ⟨i,v⟩ => ⟨⟨i.val, by rw [destination_eq]; omega⟩, v⟩
  | some ⟨j,v⟩ => some ⟨⟨destination j.val level, by simp only [destination_eq]; omega⟩, absoluteVertex j.val level v⟩

theorem absolutePivot_join {N level : ℕ} (count : ℕ) (current : Pivot N level) (o : Option (Vertex N level))
    (p : PivotChoice (Vertex N (level+1)) count) :
    absolutePivot (count+1) current (joinPivot o p) =
      absolutePivot count (States.FiniteState.childPivot current o) p := by
  cases p with
  | none =>
    cases o with
    | none => cases current <;> rfl
    | some i => rfl
  | some v =>
    obtain ⟨j,v⟩ := v
    simp only [joinPivot, absolutePivot, Fin.val_succ, absoluteVertex_join]
    rfl

/-- Convert a relative tuple/pivot record into the public absolute skeleton
at that depth for the fixed hidden sign. -/
def absoluteSkeleton {N level levels : ℕ} (h : Bool) (current : Pivot N level)
    (bound : level + levels ≤ depth N) (a : SelectedSkeleton (Vertex N level) 64 levels) : Skeleton N :=
  ⟨⟨destination a.1.val level, by simp only [destination_eq]; have := a.1.isLt; omega⟩,
    h, (fun j => absoluteVertex a.1.val level (a.2.1 j)), absolutePivot a.1.val current a.2.2⟩

/-- Select once by global skeleton and use that identical identifier throughout
all child calls and pivot changes. -/
def absoluteSelection {N level levels : ℕ} {E : Type*} (h : Bool) (current : Pivot N level)
    (bound : level + levels ≤ depth N) (select : Skeleton N → E) (a : SelectedSkeleton (Vertex N level) 64 levels) : E :=
  select (absoluteSkeleton h current bound a)

/-- Selected expert identifiers agree for every child tuple and descriptor,
including a new pivot, an inherited pivot, and deeper future pivots. -/
theorem child_absoluteSelection {N level levels : ℕ} {E : Type*} (h : Bool) (current : Pivot N level)
    (bound : level + (levels+1) ≤ depth N) (select : Skeleton N → E) (o : Option (Vertex N level)) :
    childSelection o (absoluteSelection h current bound select) =
      absoluteSelection h (States.FiniteState.childPivot current o) (by omega : level+1+levels ≤ depth N) select := by
  funext a
  obtain ⟨k,x,p⟩ := a
  change select (⟨⟨destination (k.val+1) level, _⟩, h,
      (fun j => absoluteVertex (k.val+1) level (joinDescendant (V := Vertex N level) (x j))),
      absolutePivot (k.val+1) current (joinPivot o p)⟩ : Skeleton N) =
    select (⟨⟨destination k.val (level+1), _⟩, h, (fun j => absoluteVertex k.val (level+1) (x j)),
      absolutePivot k.val (States.FiniteState.childPivot current o) p⟩ : Skeleton N)
  rw [show (fun j => absoluteVertex (k.val+1) level (joinDescendant (V := Vertex N level) (x j))) =
      (fun j => absoluteVertex k.val (level+1) (x j)) from funext fun j => absoluteVertex_join k.val level (x j)]
  rw [absolutePivot_join k.val current o p]
  rfl

/-- A current-level tuple is looked up at its original vertex coordinates and
at the actual current pivot, without dummy path data. -/
def localSkeleton {N level : ℕ} (h : Bool) (current : Pivot N level) (lt : level < depth N)
    (x : Fin 64 → Vertex N level) : Skeleton N := ⟨⟨level,lt⟩,h,x,current⟩

theorem absoluteSkeleton_local {N level levels : ℕ} (h : Bool) (current : Pivot N level)
    (bound : level + (levels+1) ≤ depth N) (x : Fin 64 → Descendant (Vertex N level) 0) :
    absoluteSkeleton h current bound ⟨0,x,none⟩ = localSkeleton h current (by omega) (fun j => (x j).1) := by
  cases current <;> rfl

/-- The root weights used for all comparison-preserving trials on an interval. -/
def rootWeight {N R : ℕ} {anchor : Fin N} {E : Type*} [DecidableEq E]
    (h : Hidden N R anchor) (select : Skeleton N → E) (e : E) : ℚ :=
  selectedWeight (V := Vertex N 0) (maskedMass h.active (weight N 0 h.positive))
    (absoluteSelection h.positive none (by simp : 0+depth N ≤ depth N) select) e

theorem rootWeight_nonneg {N R : ℕ} {anchor : Fin N} {E : Type*} [DecidableEq E]
    (h : Hidden N R anchor) (select : Skeleton N → E) (e : E) : 0 ≤ rootWeight h select e :=
  selectedWeight_nonneg _ (maskedMass_nonneg _ _ (weight_nonneg N 0 h.positive)) _ _

theorem sum_rootWeight_le_one {N R : ℕ} {anchor : Fin N} {E : Type*} [DecidableEq E] [Fintype E]
    (h : Hidden N R anchor) (select : Skeleton N → E) : ∑ e, rootWeight h select e ≤ 1 := by
  apply sum_selectedWeight_le_one _ (maskedMass_nonneg _ _ (weight_nonneg N 0 h.positive))
  exact (sum_maskedMass h.active (weight N 0 h.positive)).trans_le
    (root_mass_le_one N (Nat.zero_lt_of_lt anchor.isLt) h.positive h.active)

/-- Weight on a root skeleton is independent both of the trial and the selected
expert identifier. -/
def rootSkeletonWeight {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (a : SelectedSkeleton (Vertex N 0) 64 (depth N)) : ℚ :=
  expertWeight (maskedMass h.active (weight N 0 h.positive)) 64 a.1.val a.2.1 a.2.2

theorem rootSkeletonWeight_nonneg {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (a : SelectedSkeleton (Vertex N 0) 64 (depth N)) : 0 ≤ rootSkeletonWeight h a :=
  expertWeight_nonneg _ (maskedMass_nonneg h.active _ (weight_nonneg N 0 h.positive)) _ _ _ _

theorem rootWeight_eq_skeleton_charge {N R : ℕ} {anchor : Fin N} {E : Type*} [Fintype E] [DecidableEq E]
    (h : Hidden N R anchor) (select : Skeleton N → E) (s : E → ℚ) :
    ∑ e, rootWeight h select e * s e = ∑ a, rootSkeletonWeight h a *
      s (select (absoluteSkeleton h.positive none (by simp : 0+depth N ≤ depth N) a)) := by
  classical
  change (∑ e, selectedWeight _ _ e * s e) = _
  rw [selectedWeight_scores]
  simp only [rootSkeletonWeight, scoreMass, Fintype.sum_sigma, Fintype.sum_prod_type, absoluteSelection]
  rfl

theorem sum_rootSkeletonWeight_le_one {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor) :
    ∑ a, rootSkeletonWeight h a ≤ 1 := by
  have he := rootWeight_eq_skeleton_charge h (fun _ => ()) (fun _ => 1)
  simp only [mul_one] at he
  rw [← he]
  exact sum_rootWeight_le_one h _

/-- State-specific charging weights on the actual expert identifiers. -/
def stateWeight {N R l L : ℕ} {anchor : Fin N} {E : Type*} [DecidableEq E]
    (h : Hidden N R anchor) (s : States.FiniteState N l) (bound : l+L ≤ depth N)
    (sel : Skeleton N → E) : E → ℚ :=
  selectedWeight (s.ambientMass h) (absoluteSelection h.positive s.pivot bound sel)

/-- The root state reproduces the fixed root weights. -/
theorem stateWeight_root {N R : ℕ} {anchor : Fin N} {E : Type*} [DecidableEq E]
    (h : Hidden N R anchor) (sel : Skeleton N → E) :
    stateWeight h (States.FiniteState.root h) (by simp : 0+depth N ≤ depth N) sel = rootWeight h sel := rfl

/-- Lift an identifier-indexed score family to the relative expert indices. -/
def stateScores {N R l L : ℕ} {anchor : Fin N} {E : Type*}
    (h : Hidden N R anchor) (s : States.FiniteState N l) (bound : l+L ≤ depth N)
    (sel : Skeleton N → E) (v : E → ℚ) : ScoreFamily (Vertex N l) 64 L :=
  fun k x ρ => v (absoluteSelection h.positive s.pivot bound sel ⟨k,x,ρ⟩)

theorem stateWeight_scores {N R l L : ℕ} {anchor : Fin N} {E : Type*} [DecidableEq E] [Fintype E]
    (h : Hidden N R anchor) (s : States.FiniteState N l) (bound : l+L ≤ depth N)
    (sel : Skeleton N → E) (v : E → ℚ) :
    ∑ e, stateWeight h s bound sel e * v e = scoreMass (s.ambientMass h) (stateScores h s bound sel v) :=
  selectedWeight_scores _ _ _

theorem child_stateScores {N R l L : ℕ} {anchor : Fin N} {E : Type*}
    (h : Hidden N R anchor) (s : States.FiniteState N l) (bound : l+(L+1) ≤ depth N)
    (sel : Skeleton N → E) (v : E → ℚ) (hist : History N) (y : Vertex N l → ℚ) (o : Option (Vertex N l)) :
    childScores o (stateScores h s bound sel v) =
      stateScores h (s.child h hist y o) (by omega : l+1+L ≤ depth N) sel v := by
  funext k x ρ
  exact congrArg v (congrFun (child_absoluteSelection h.positive s.pivot bound sel o) ⟨k,x,ρ⟩)

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
