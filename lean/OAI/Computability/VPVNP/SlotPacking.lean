import OAI.Computability.VPVNP.SlotGraph
import Mathlib.Data.ZMod.Basic

/-!
# Positions, bundles and placements for the shrinking step

Appendix C of *VP and VNP differ over every field* splits a lane into color
bits, an outgoing-slot label, a tag and an unconsumed lane. A wire whose
endpoints are both thick goes into the bundle indexed by its base arc, source
tag and remaining lane. Every other wire supplies exactly one CD demand. Its
C endpoint is thin, with ties settled by the original direction of the arc.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

/-- A word of the given length with entries in the additive group of integers modulo two. -/
abbrev BitWord (c : ℕ) := Fin c → ZMod 2
/-- A packed site specified by a base vertex, a tag, and the unconsumed lane coordinate. -/
abbrev Site (V Tag L : Type*) := V × (Tag × L)
/-- An old position specified by its packed site, color-bit word, and lane coordinate used to
label a slot. -/
abbrev Position (V H Tag L : Type*) (c : ℕ) := Site V Tag L × (BitWord c × H)
/-- An old arc address consisting of a site, an incident slot number, and the color and
slot-label coordinates of its lane. -/
abbrev Arc (V H Tag L : Type*) (d c : ℕ) := (Site V Tag L × Fin d) × (BitWord c × H)

/-- Input to Appendix C after selecting the proper coloring and tag offsets.
The bijection `slotLabel` lets the lane use a binary vector group even when
the graph's outgoing slots are labeled by `Fin d`. -/
structure PackingData (V H Tag L : Type*) (d c : ℕ) where
  /-- The directed regular base graph matching outgoing and incoming slots for the shrinking
  step. -/
  slots : SlotGraph V d
  /-- The proper coloring of the base vertices used to select the bit that determines whether a
  position is thick. -/
  color : V → Fin c
  proper : ∀ p, color p.1 ≠ color (slots.target p).1
  /-- Bijection from the slot-label coordinate of a lane to the index of one of the outgoing
  slots. -/
  slotLabel : H ≃ Fin d
  /-- Tag increment at each base vertex used when assigning a thin position to its outgoing
  bundle. -/
  offset : V → Tag
  /-- Change in the color-bit word along each base arc, added to the source word when lifting
  the arc. -/
  bitShift : V × Fin d → BitWord c
  /-- Additive displacement of the slot-label coordinate along each base arc. -/
  slotShift : V × Fin d → H
  /-- Displacement of the tag and unconsumed lane coordinates along a base arc of the lifted
  site graph. -/
  siteShift : V × Fin d → Tag × L

variable {V H Tag L : Type*} {d c : ℕ}

/-- Forget the slot of an outgoing (or, dually, incoming) endpoint. -/
def sourcePosition (a : Arc V H Tag L d c) : Position V H Tag L c := (a.1.1, a.2)

namespace PackingData

variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- Once the color bits and slot label are suppressed, bundles themselves
form a regular lift with only tag and remaining-lane coordinates. -/
def siteGraph : SlotGraph (Site V Tag L) d := (LiftedSlots.mk P.slots P.siteShift).actualGraph

/-- Each old arc's permutation of the complete coordinate tuple. -/
def actual : Equiv.Perm (Arc V H Tag L d c) :=
  (LiftedSlots.mk P.siteGraph (fun p ↦
    (P.bitShift (p.1.1,p.2), P.slotShift (p.1.1,p.2)))).actualTarget

@[simp] theorem actual_apply (p : Site V Tag L × Fin d) (w : BitWord c) (h : H) :
    P.actual (p,w,h) = (P.siteGraph.target p,w + P.bitShift (p.1.1,p.2),
      h + P.slotShift (p.1.1,p.2)) := rfl

@[simp] theorem actual_symm_apply (p : Site V Tag L × Fin d) (w : BitWord c) (h : H) :
    P.actual.symm (p,w,h) = (P.siteGraph.target.symm p,
      w - P.bitShift (P.slots.target.symm (p.1.1,p.2)),
      h - P.slotShift (P.slots.target.symm (p.1.1,p.2))) := rfl

/-- Test the bit belonging to the position's base color. -/
def thick (x : Position V H Tag L c) : Prop := x.2.1 (P.color x.1.1) = 1

instance (x : Position V H Tag L c) : Decidable (P.thick x) := by unfold thick; infer_instance

/-- The bundle assignment offsets the tag while preserving the unconsumed lane. -/
def offsetSite : Equiv.Perm (Site V Tag L) where
  toFun x := (x.1, x.2.1 + P.offset x.1, x.2.2)
  invFun x := (x.1, x.2.1 - P.offset x.1, x.2.2)
  left_inv := by rintro ⟨x,t,g⟩; simp
  right_inv := by rintro ⟨x,t,g⟩; simp

/-- Each thin position is assigned to its own outgoing slot at the offset tag. -/
def assignedBundle (x : Position V H Tag L c) : Site V Tag L × Fin d :=
  (P.offsetSite x.1, P.slotLabel x.2.2)

/-- The demand motifs are indexed by all actual wires outside thick–thick bundles. -/
abbrev Motif := {a : Arc V H Tag L d c //
  ¬ (P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a)))}

/-- On a thin–thin wire `C` is the outgoing endpoint. -/
def C (m : P.Motif) : Position V H Tag L c :=
  if P.thick (sourcePosition m.val) then sourcePosition (P.actual m.val) else sourcePosition m.val

/-- The old endpoint opposite `C`. -/
def D (m : P.Motif) : Position V H Tag L c :=
  if P.thick (sourcePosition m.val) then sourcePosition m.val else sourcePosition (P.actual m.val)

/-- In both possible directions the designated C endpoint is thin. -/
theorem not_thick_C (m : P.Motif) : ¬ P.thick (P.C m) := by
  unfold C
  split_ifs with h
  · exact fun ht ↦ m.property ⟨h,ht⟩
  · exact h

/-- The single bundle which receives this CD demand. -/
def bundle (m : P.Motif) : Site V Tag L × Fin d := P.assignedBundle (P.C m)

/-- The source site of the bundle assigned to a demand motif, serving as its A site. -/
def roleA (m : P.Motif) : Site V Tag L := (P.bundle m).1

/-- The target site of the bundle assigned to a demand motif, serving as its B site. -/
def roleB (m : P.Motif) : Site V Tag L := (P.siteGraph.target (P.bundle m)).1

/-- `false` puts every thin position at the source of its assigned bundle,
`true` puts it at the destination. Every thick position stays at its packed site. -/
def placement (layout : Bool) (x : Position V H Tag L c) : Site V Tag L :=
  if P.thick x then x.1 else if layout then (P.siteGraph.target (P.assignedBundle x)).1
    else (P.assignedBundle x).1

/-- A `D` map moves with the whole old factor at that position. -/
def roleD (layout : Bool) (m : P.Motif) : Site V Tag L := P.placement layout (P.D m)

@[simp] theorem placement_C_source (m : P.Motif) : P.placement false (P.C m) = P.roleA m := by
  simp [placement, P.not_thick_C, roleA, bundle]

@[simp] theorem placement_C_target (m : P.Motif) : P.placement true (P.C m) = P.roleB m := by
  simp [placement, P.not_thick_C, roleB, bundle]

end PackingData

end Compression

end VPVNP
end Computability
end OAI
