import OAI.Hierarchy.ProbeLocalFlattening
import OAI.Hierarchy.ProbeBalls

namespace OAI
/-! # The actual column, catalyst and horizontal wires of a local price test -/

noncomputable section
namespace Hierarchy.AdaptiveProbe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical

/-- The layer with no direction is the column center. -/
abbrev ColumnLayer (k : ℕ) := Option (Fin k × Bool)
abbrev ColumnSite (I : Type*) (k : ℕ) := I × ColumnLayer k

structure DistinctPair (X : Type*) where
  left : X
  right : X
  apart : left ≠ right

/-- Naming of the finite physical sites of a local test. For ordinary applications
use the canonical ordinal names. To mount the same format on a subset of a globally
ordered board, name the sites in the order of their actual images instead. -/
class SiteNaming (X : Type*) [Fintype X] where
  labels : X ≃ Fin (Fintype.card X)

noncomputable instance (priority := 100) SiteNaming.canonical (X : Type*) [Fintype X] : SiteNaming X :=
  ⟨Fintype.equivFin X⟩

namespace DistinctPair
variable {X : Type*} [Fintype X] [SiteNaming X]

/-- The finite site's ordinal is independent of the direction in which the wire is read. -/
def chord (a : DistinctPair X) : Chord (Fintype.card X) :=
  let e := SiteNaming.labels (X:=X)
  if h : e a.left < e a.right then ⟨(e a.left,e a.right),h⟩ else
    ⟨(e a.right,e a.left),lt_of_le_of_ne (le_of_not_gt h)
      (fun eq => a.apart (e.injective eq.symm))⟩

theorem chord_joins (a : DistinctPair X) :
    Joins a.chord (SiteNaming.labels (X:=X) a.left) (SiteNaming.labels (X:=X) a.right) := by
  unfold chord Joins
  dsimp only
  split <;> simp
end DistinctPair

namespace ColumnWires
variable {I H E A : Type*} [Fintype I] {k : ℕ} [SiteNaming (ColumnSite I k)]

/-- All primitive local menu entries. The `extra` part holds the actual payload,
altimeter and purchased-probe sockets in that test. -/
inductive Role (I H E : Type*) (k : ℕ) where
  | catalyst (i : I) (j : Fin k)
  | radius (i : I) (j : Fin k) (side : Bool)
  | cross (i : I) (axes : {a : Fin k × Fin k // a.1 ≠ a.2}) (s t : Bool)
  | horizontal (edge : H) (layer : ColumnLayer k)
  | extra (e : E)
  deriving Fintype

variable (horizontal : H → DistinctPair I) (extra : E → DistinctPair (ColumnSite I k))

def ends : Role I H E k → DistinctPair (ColumnSite I k)
  | .catalyst i j => ⟨(i,some (j,false)),(i,some (j,true)),by simp⟩
  | .radius i j s => ⟨(i,none),(i,some (j,s)),by simp⟩
  | .cross i a s t => ⟨(i,some (a.val.1,s)),(i,some (a.val.2,t)),by
      intro h; exact a.property (congrArg Prod.fst (Option.some.inj (Prod.mk.inj h).2))⟩
  | .horizontal h layer => ⟨((horizontal h).left,layer),((horizontal h).right,layer),
      fun eq => (horizontal h).apart (congrArg Prod.fst eq)⟩
  | .extra e => extra e

def wires (r : Role I H E k) := (ends horizontal extra r).chord

def quote (M : ℝ) (len : H → ℝ) (price : E → ℝ) : Role I H E k → ℝ
  | .catalyst _ _ => 2*M
  | .radius _ _ _ => M
  | .cross _ _ _ _ => ⌈Real.sqrt 2*M⌉
  | .horizontal h _ => len h
  | .extra e => price e

def demand (req : A → E) : (I × Fin k) ⊕ A → Role I H E k
  | .inl (i,j) => .catalyst i j
  | .inr a => .extra (req a)

def site (i : I) (l : ColumnLayer k) := SiteNaming.labels (X:=ColumnSite I k) (i,l)

variable {horizontal extra}

theorem radius_bounds (M : ℝ) (len : H → ℝ) (price : E → ℝ) (i : I) (j : Fin k) (s : Bool) :
    WireBound (wires horizontal extra) (quote M len price) (site i none) (site i (some (j,s))) M :=
  .wire (Role.radius (H:=H) (E:=E) i j s) _ _ ((ends horizontal extra (.radius i j s)).chord_joins)

theorem catalyst_demanded (M : ℝ) (len : H → ℝ) (price : E → ℝ) (req : A → E) (i : I) (j : Fin k) :
    demanded (wires horizontal extra) (demand req) (quote M len price)
      (site i (some (j,false))) (site i (some (j,true))) (2*M) :=
  ⟨.inl (i,j),(ends horizontal extra (.catalyst i j)).chord_joins,rfl⟩

theorem cross_bound (M : ℝ) (len : H → ℝ) (price : E → ℝ) (i : I) (j l : Fin k) (ne : j ≠ l)
    (s t : Bool) : WireBound (wires horizontal extra) (quote M len price)
      (site i (some (j,s))) (site i (some (l,t))) (Real.sqrt 2*M+1) := by
  let r : Role I H E k := .cross i ⟨(j,l),ne⟩ s t
  apply WireBound.weaken (.wire r _ _ (ends horizontal extra r).chord_joins)
  exact (Int.ceil_lt_add_one _).le

theorem horizontal_bound (M : ℝ) (len : H → ℝ) (price : E → ℝ) (h : H) (layer : ColumnLayer k) :
    WireBound (wires horizontal extra) (quote M len price)
      (site (horizontal h).left layer) (site (horizontal h).right layer) (len h) :=
  .wire (Role.horizontal (I:=I) (E:=E) h layer) _ _ (ends horizontal extra (.horizontal h layer)).chord_joins

/-- The undirected incidence of an actual wire gives an equivalence-closure step
regardless of its ordinal orientation. -/
private theorem reachable_of_joins {S : ℕ} {T : Type*} (edge : T → Chord S) (e : T)
    {x y : Fin S} (joins : Joins (edge e) x y) :
    Relation.EqvGen (fun a b => ∃ t, (edge t).val=(a,b)) x y := by
  rcases joins with fwd | rev
  · exact .rel _ _ ⟨e,fwd⟩
  · exact .symm _ _ (.rel _ _ ⟨e,rev⟩)

/-- A connected set of physical columns gives a connected local spectral format.
The finite site set includes every radial endpoint, even when no test uses it. -/
theorem connected (root : I) (reach : ∀ i, Relation.EqvGen
    (fun a b => ∃ h : H, (horizontal h).left=a ∧ (horizontal h).right=b) root i) :
    Probe.Connected (wires horizontal extra) := by
  let R := fun a b => ∃ e, (wires horizontal extra e).val=(a,b)
  have along {i i' : I} (h : Relation.EqvGen (fun a b => ∃ h : H,
      (horizontal h).left=a ∧ (horizontal h).right=b) i i') :
      Relation.EqvGen R (site (k:=k) i none) (site i' none) := by
    induction h with
    | rel x y h =>
      obtain ⟨e,rfl,rfl⟩ := h
      exact reachable_of_joins (wires horizontal extra) (Role.horizontal (k:=k) e none) (ends horizontal extra (.horizontal e none)).chord_joins
    | refl x => exact .refl _
    | symm x y _ ih => exact .symm _ _ ih
    | trans x y z _ _ ih ih' => exact .trans _ _ _ ih ih'
  have radial (v : ColumnSite I k) : Relation.EqvGen R (site v.1 none) (site v.1 v.2) := by
    rcases v with ⟨i,_|⟨j,t⟩⟩
    · exact .refl _
    · exact reachable_of_joins (wires horizontal extra) (Role.radius i j t) (ends horizontal extra (.radius i j t)).chord_joins
  intro x y
  obtain ⟨v,rfl⟩ := (SiteNaming.labels (X:=ColumnSite I k)).surjective x
  obtain ⟨u,rfl⟩ := (SiteNaming.labels (X:=ColumnSite I k)).surjective y
  have vx := Relation.EqvGen.trans _ _ _ (along (reach v.1)) (radial v)
  have ux := Relation.EqvGen.trans _ _ _ (along (reach u.1)) (radial u)
  exact .trans _ _ _ (.symm _ _ vx) ux

/-- The BFS radius rigorously bounds simultaneous horizontal motion of all signed
end marks, with exactly the same path as the unmarked centers. -/
theorem bounded_ball [DecidableEq I] (M : ℝ) (len : H → ℝ) (price : E → ℝ) (next : I → Finset I)
    (steps : ∀ x y, y ∈ next x → ∃ h : H, len h ≤ 1 ∧
      ((horizontal h).left=x ∧ (horizontal h).right=y ∨
       (horizontal h).left=y ∧ (horizontal h).right=x))
    {x y : I} {r : ℕ} (inside : y ∈ neighborhood next x r) (layer : ColumnLayer k) :
    WireBound (wires horizontal extra) (quote M len price) (site x layer) (site y layer) (r:ℝ) := by
  classical
  apply ball_path_bound (P:=fun i j n => WireBound (wires horizontal extra) (quote M len price)
    (site i layer) (site j layer) (n:ℝ)) next _ _ _ _ inside
  · intro i; rw [Nat.cast_zero]; exact .self _
  · intro i j h
    obtain ⟨e,cost,pair|pair⟩ := steps i j h
    · obtain ⟨rfl,rfl⟩ := pair
      rw [Nat.cast_one]; exact (horizontal_bound M len price e layer).weaken cost
    · obtain ⟨rfl,rfl⟩ := pair
      rw [Nat.cast_one]; exact (horizontal_bound M len price e layer).symm.weaken cost
  · intro i j z a b h h'
    simpa only [Nat.cast_add] using h.append h'
  · intro i j n h
    exact h.weaken (by exact_mod_cast Nat.le_succ n)

end ColumnWires
end Hierarchy.AdaptiveProbe
end

end OAI
