import OAI.Computability.BorderVNP.DiagonalTaggedRound
import OAI.Computability.BorderVNP.PackedCellWireView
import OAI.Computability.BorderVNP.ShortenStaticRowsAccess

/-! # Exact prior site reads after a public combining step

Every bit of an old incident cable belongs to one ordered band. An unselected
band uses the retained cable. A selected band uses the hook at the old site's
end, with the source chosen at a self-loop as in the cut tensor. The original
external port words are read at their old sites. These reassembled words are
the complete inputs to the inherited field and tagged tables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep Shortening.SeedIntervals
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev out := output e p bin perm positive first q
private noncomputable abbrev cut := (partition p.layout bin perm m).selected
private noncomputable abbrev bands := layout p.layout bin perm m

/-- An incident cable of the old site; loops carry a single local argument. -/
abbrev Incident {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits) (v : N.Site) :=
  {z : N.Edge // N.src z = v ∨ N.dst z = v}

/-- The live successor cable carrying one band at the old site. On a cut
self-loop the old table selects its source hook. -/
noncomputable def oldBandWire (v : p.layout.Site) (z : Incident p.layout v) (b : Band D) :
    Incident (out e p bin perm positive first q).layout (.inl v) :=
  if h : (z.val,b) ∈ cut (m := m) p bin perm then
    if hs : p.layout.src z.val = v then
      ⟨.inl (.inl ⟨(z.val,b),h⟩),Or.inl (congrArg Sum.inl hs)⟩
    else
      ⟨.inl (.inr ⟨(z.val,b),h⟩),Or.inl (congrArg Sum.inl (z.property.resolve_left hs))⟩
  else ⟨.inr (.inl ⟨(z.val,b),h⟩),z.property.imp (congrArg Sum.inl) (congrArg Sum.inl)⟩

/-- All three physical cable kinds have exactly the width of the old band. -/
theorem oldBandWire_width (v : p.layout.Site) (z : Incident p.layout v) (b : Band D) :
    (out e p bin perm positive first q).layout.width (oldBandWire e p bin perm positive first q v z b).val =
      (bands (m := m) p bin perm).width (z.val,b) := by
  unfold oldBandWire
  split
  · split <;> rfl
  · rfl

/-- Physical bit word of one band as read by the old site in the true cut table. -/
noncomputable def oldBandWord (y : (out e p bin perm positive first q).layout.Assignment)
    (v : p.layout.Site) (z : Incident p.layout v) (b : Band D)
    (k : Fin ((bands (m := m) p bin perm).width (z.val,b))) : Bool :=
  if h : (z.val,b) ∈ cut (m := m) p bin perm then
    if _hs : p.layout.src z.val = v then y (.inl (.inl ⟨(z.val,b),h⟩)) k
    else y (.inl (.inr ⟨(z.val,b),h⟩)) k
  else y (.inr (.inl ⟨(z.val,b),h⟩)) k

set_option backward.isDefEq.respectTransparency false in
/-- A public incident-cable read at the ordered band ordinal gives its correct bit. -/
theorem oldBandWord_read (y : (out e p bin perm positive first q).layout.Assignment)
    (v : p.layout.Site) (z : Incident p.layout v) (b : Band D)
    (k : Fin ((bands (m := m) p bin perm).width (z.val,b))) :
    oldBandWord e p bin perm positive first q y v z b k =
      y (oldBandWire e p bin perm positive first q v z b).val
        (Fin.cast (oldBandWire_width e p bin perm positive first q v z b).symm k) := by
  let G := (out e p bin perm positive first q).layout
  let c := oldBandWire e p bin perm positive first q v z b
  have same {edge : G.Edge} (he : c.val = edge) (l : Fin (G.width edge)) (hl : l.val = k.val) :
      y edge l = y c.val (Fin.cast (oldBandWire_width e p bin perm positive first q v z b).symm k) := by
    subst edge
    exact congrArg (y c.val) (Fin.ext hl)
  unfold oldBandWord
  split
  · rename_i h
    split
    · rename_i hs
      exact same (edge := .inl (.inl ⟨(z.val,b),h⟩)) (by simp only [c,oldBandWire,dite_eq_left h,dite_eq_left hs]) k rfl
    · rename_i hs
      exact same (edge := .inl (.inr ⟨(z.val,b),h⟩)) (by simp only [c,oldBandWire,dite_eq_left h,dite_eq_right hs]) k rfl
  · rename_i h
    exact same (edge := .inr (.inl ⟨(z.val,b),h⟩)) (by simp only [c,oldBandWire,dite_eq_right h]) k rfl

/-- Reassembled word of an old incident cable, at the original local bit indices. -/
noncomputable def oldWireWords (y : (out e p bin perm positive first q).layout.Assignment)
    (v : p.layout.Site) (z : Incident p.layout v) (k : Fin (p.layout.width z.val)) : Bool :=
  let b := (p.layout.bandIndex (label p.layout bin perm m) z.val).symm k
  oldBandWord e p bin perm positive first q y v z b.1 b.2

/-- Original local exterior port words, with their unchanged physical lane order. -/
def oldPortWords (x : Ports bits) (v : p.layout.Site) (z : {u : P // p.layout.attach u = v}) :
    Fin (bits z.val) → Bool := x z.val

/-- Staging the band at its old ordinal recovers the whole word expected by the
prior table. This includes all retained pieces, selected hooks and zero-width rows. -/
theorem oldWireWords_at (y : (out e p bin perm positive first q).layout.Assignment)
    (v : p.layout.Site) (z : Incident p.layout v) (b : Band D)
    (k : Fin ((bands (m := m) p bin perm).width (z.val,b))) :
    oldWireWords e p bin perm positive first q y v z ((p.layout.bandOrder (label p.layout bin perm m) z.val b) k).val =
      oldBandWord e p bin perm positive first q y v z b k := by
  let g := fun t : Σ i, Fin ((bands (m := m) p bin perm).width (z.val,i)) =>
    oldBandWord e p bin perm positive first q y v z t.1 t.2
  exact congrArg g ((p.layout.bandIndex (label p.layout bin perm m) z.val).symm_apply_apply ⟨b,k⟩)

private noncomputable abbrev inserted :=
  (partition p.layout bin perm m).parallel (seedNetwork e (blocks p.layout bin perm m)
    (p := pieces (m := m) p bin perm) (partition p.layout bin perm m) (bundle p.layout bin perm m positive) q)

set_option backward.isDefEq.respectTransparency false in
/-- At an inherited site, the old local row is reconstructed identically for any
type of table entries and any tables installed inside the selected cut. -/
theorem sewn_table_read {R : Type*} (table : p.layout.Tables R)
    (inner : (inserted e p bin perm positive q).Tables R) (y : (out e p bin perm positive first q).layout.Assignment)
    (x : Ports bits) (v : p.layout.Site) :
    let B := bands (m := m) p bin perm
    let S := cut (m := m) p bin perm
    (out e p bin perm positive first q).layout.read ((B.cut S).sewTables (inserted e p bin perm positive q)
      (B.cutTables S (p.layout.bandTables (label p.layout bin perm m) table)) inner) y x (.inl v) =
        table v (oldWireWords e p bin perm positive first q y v) (oldPortWords p x v) := by
  apply congrArg (fun f => table v f (oldPortWords p x v))
  funext z k
  dsimp only [oldWireWords, oldBandWord, Network.bandTables, Network.cutTables, Network.sewTables, Network.read, cut, bands]
  have hsrc (b : Band D) : (layout p.layout bin perm m).src (z.val,b) = p.layout.src z.val := rfl
  simp only [dite_apply,hsrc]
  congr!

/-- Exact factor at any inherited physical site of the field-valued sewn output. -/
theorem old_table_read (y : (out e p bin perm positive first q).layout.Assignment)
    (x : Ports bits) (v : p.layout.Site) :
    (out e p bin perm positive first q).layout.read (out e p bin perm positive first q).table y x (.inl v) =
      p.table v (oldWireWords e p bin perm positive first q y v) (oldPortWords p x v) :=
  sewn_table_read e p bin perm positive first q p.table _ y x v

open Diagonal.CellEntries

/-- The genuine tagged round uses the old table, preserving the complete gadget and
parameter record at each inherited site on every assignment of the successor wires. -/
theorem old_tagged_read {Param Gadget : Type*} (tags : p.layout.Tables (Entry Param Gadget))
    (position : e.Entry → Gadget) (y : (out e p bin perm positive first q).layout.Assignment)
    (x : Ports bits) (v : p.layout.Site) :
    let src : Pack D P bits (Entry Param Gadget) := ⟨p.layout,tags⟩
    let next := roundTags src bin perm e position positive first q
    next.layout.read next.table y x (.inl v) =
      tags v (oldWireWords e p bin perm positive first q y v) (oldPortWords p x v) :=
  sewn_table_read e p bin perm positive first q tags _ y x v

end Packing.Inherited

end BorderVNP
end Computability
end OAI
