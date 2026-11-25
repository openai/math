import OAI.Computability.VPVNP.SlotPacking
import Mathlib.Tactic

namespace OAI
/-! # Translation of the remaining lane in a shrinking layout -/

namespace ThreeFlat.Diagonal.CompressorPacking
open Computability.VPVNP.Compression
variable {V H Tag L : Type*} {c d : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]

def moveSite (g : L) (x : Site V Tag L) : Site V Tag L := (x.1,x.2.1,x.2.2+g)
def moveSlot (g : L) (p : Site V Tag L × Fin d) := (moveSite g p.1,p.2)
def movePosition (g : L) (x : Position V H Tag L c) : Position V H Tag L c := (moveSite g x.1,x.2)
def moveArc (g : L) (e : Arc V H Tag L d c) : Arc V H Tag L d c := (moveSlot g e.1,e.2)

variable (P : PackingData V H Tag L d c)

omit [AddCommGroup H] in
@[simp] theorem site_target_move (g : L) (p : Site V Tag L × Fin d) :
    P.siteGraph.target (moveSlot g p) = moveSlot g (P.siteGraph.target p) := by
  obtain ⟨⟨x,j,l⟩,i⟩ := p
  change (((_,_,(l+g)+(P.siteShift (x,i)).2),_) : Site V Tag L × Fin d) = _
  rw [add_right_comm l g]
  rfl

theorem actual_move (g : L) (e : Arc V H Tag L d c) :
    P.actual (moveArc g e) = moveArc g (P.actual e) := by
  obtain ⟨p,w,h⟩ := e
  exact Prod.ext (site_target_move P g p) rfl

omit [AddCommGroup H] [AddCommGroup Tag] in
@[simp] theorem thick_move (g : L) (x : Position V H Tag L c) :
    P.thick (movePosition g x) ↔ P.thick x := Iff.rfl

omit [AddCommGroup H] [AddCommGroup Tag] in
@[simp] theorem source_move (g : L) (e : Arc V H Tag L d c) :
    sourcePosition (moveArc g e) = movePosition g (sourcePosition e) := rfl

def moveMotif (g : L) (m : P.Motif) : P.Motif :=
  ⟨moveArc g m.val, by simpa only [actual_move, source_move, thick_move] using m.property⟩

@[simp] theorem moveMotif_zero (m : P.Motif) : moveMotif P 0 m = m := by
  apply Subtype.ext
  simp [moveMotif,moveArc,moveSlot,moveSite]

theorem moveMotif_add (g h : L) (m : P.Motif) :
    moveMotif P h (moveMotif P g m) = moveMotif P (g+h) m := by
  apply Subtype.ext
  simp [moveMotif,moveArc,moveSlot,moveSite,add_assoc]

theorem moveC (g : L) (m : P.Motif) :
    P.C (moveMotif P g m) = movePosition g (P.C m) := by
  by_cases h : P.thick (sourcePosition m.val) <;>
    simp [PackingData.C,moveMotif,actual_move,h]

theorem moveD (g : L) (m : P.Motif) :
    P.D (moveMotif P g m) = movePosition g (P.D m) := by
  by_cases h : P.thick (sourcePosition m.val) <;>
    simp [PackingData.D,moveMotif,actual_move,h]

omit [AddCommGroup H] in
@[simp] theorem assigned_move (g : L) (x : Position V H Tag L c) :
    P.assignedBundle (movePosition g x) = moveSlot g (P.assignedBundle x) := rfl

theorem bundle_move (g : L) (m : P.Motif) :
    P.bundle (moveMotif P g m) = moveSlot g (P.bundle m) := by
  unfold PackingData.bundle
  rw [moveC, assigned_move]

omit [AddCommGroup H] in
theorem placement_move (g : L) (layout : Bool) (x : Position V H Tag L c) :
    P.placement layout (movePosition g x) = moveSite g (P.placement layout x) := by
  by_cases h : P.thick x <;> cases layout <;>
    simp only [PackingData.placement, thick_move, h, ite_false, ite_true, assigned_move,
      site_target_move] <;> rfl

theorem roleA_move (g : L) (m : P.Motif) :
    P.roleA (moveMotif P g m) = moveSite g (P.roleA m) := by
  rw [PackingData.roleA,bundle_move]
  rfl

theorem roleB_move (g : L) (m : P.Motif) :
    P.roleB (moveMotif P g m) = moveSite g (P.roleB m) := by
  rw [PackingData.roleB,bundle_move,site_target_move]
  rfl

theorem roleD_move (g : L) (layout : Bool) (m : P.Motif) :
    P.roleD layout (moveMotif P g m) = moveSite g (P.roleD layout m) := by
  rw [PackingData.roleD,moveD,placement_move]
  rfl

/-- Anchor an old motif by its originally outgoing remaining lane, before
the designation of either endpoint as C or D. -/
abbrev anchor (m : P.Motif) : L := m.val.1.1.2.2
abbrev Rooted := {m : P.Motif // anchor P m = 0}

@[simp] theorem anchor_move (g : L) (m : P.Motif) :
    anchor P (moveMotif P g m) = anchor P m + g := rfl

def normalize (m : P.Motif) : Rooted P :=
  ⟨moveMotif P (-(anchor P m)) m, by simp⟩

/-- Motif identifiers can be enumerated at lane zero and then translated
to recover each individual physical motif. -/
def allLanes : Rooted P × L ≃ P.Motif where
  toFun x := moveMotif P x.2 x.1.val
  invFun m := (normalize P m,anchor P m)
  left_inv x := by
    obtain ⟨⟨m,hm⟩,g⟩ := x
    apply Prod.ext
    · apply Subtype.ext
      simp [normalize,anchor_move,hm,moveMotif_add]
    · simp [anchor_move,hm]
  right_inv m := by simp [normalize,moveMotif_add]

/-- Each base role incidence identifies exactly one actual role incidence
at lane zero. -/
def roleAtZero (role : P.Motif → Site V Tag L)
    (moves : ∀ g m, role (moveMotif P g m) = moveSite g (role m)) (b : V × Tag) :
    {m : Rooted P // ((role m.val).1,(role m.val).2.1) = b} ≃
      {m : P.Motif // role m = (b.1,b.2,0)} where
  toFun m := ⟨moveMotif P (-(role m.val.val).2.2) m.val.val, by
    rw [moves]
    exact Prod.ext (congrArg (fun z : V × Tag => z.1) m.property)
      (Prod.ext (congrArg (fun z : V × Tag => z.2) m.property) (add_neg_cancel _))⟩
  invFun m := ⟨normalize P m.val, by
    change ((role (moveMotif P _ m.val)).1,(role (moveMotif P _ m.val)).2.1) = _
    rw [moves, m.property]
    rfl⟩
  left_inv m := by
    apply Subtype.ext
    apply Subtype.ext
    simp [normalize,anchor_move,m.val.property,moveMotif_add]
  right_inv m := by
    apply Subtype.ext
    simp [normalize,moves,moveSite,m.property,moveMotif_add]

end ThreeFlat.Diagonal.CompressorPacking

end OAI
