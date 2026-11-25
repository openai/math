import OAI.ThreeFlat.Diagonal.CompressorNativePlacement

namespace OAI
/-! # Local old-arc descriptors for a shrinking step

An old arc has source and target positions and the outgoing slot ordinal.
Reading an incoming candidate uses the public inverse columns, so its source
and destination are in the same orientation as an outgoing candidate. The
three surviving roles are computed directly from those two old positions.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Placement
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.DescriptorExpr

open scoped Fin.NatCast
variable {A B : Type*} {w k n : ℕ}

structure ArcColumns (A : Type*) extends Columns A where
  forwardBits : A
  forwardLabel : A
  backBits : A
  backLabel : A

def ArcColumns.map (f : A → B) (u : ArcColumns A) : ArcColumns B :=
  ⟨u.toColumns.map f,f u.forwardBits,f u.forwardLabel,f u.backBits,f u.backLabel⟩

structure Ends (A : Type*) where
  source : Position A
  target : Position A
  originalSlot : A

def Ends.map (f : A → B) (e : Ends A) : Ends B :=
  ⟨e.source.map f,e.target.map f,f e.originalSlot⟩

variable (o : Ops A) (g : ArcColumns A) (d : ℕ)

def ends (incoming : Bool) (x : Position A) (i : A) : Ends A :=
  if incoming then
    let src := backward o g.toColumns d x.site i
    let u := o.bin .bitXor x.bits (slot o d g.backBits x.site.base i)
    let h := o.bin .bitXor x.slot (slot o d g.backLabel x.site.base i)
    ⟨⟨src,u,h⟩,x,slot o d g.backSlot x.site.base i⟩
  else
    let dst := forward o g.toColumns d x.site i
    let u := o.bin .bitXor x.bits (slot o d g.forwardBits x.site.base i)
    let h := o.bin .bitXor x.slot (slot o d g.forwardLabel x.site.base i)
    ⟨x,⟨dst,u,h⟩,i⟩

def Site.select (o : Ops A) (flag : A) (yes no : Site A) : Site A :=
  ⟨o.choose flag (o.lit 1) yes.base no.base,o.choose flag (o.lit 1) yes.tag no.tag,
    o.choose flag (o.lit 1) yes.lane no.lane⟩

def Position.select (o : Ops A) (flag : A) (yes no : Position A) : Position A :=
  ⟨Site.select o flag yes.site no.site,o.choose flag (o.lit 1) yes.bits no.bits,
    o.choose flag (o.lit 1) yes.slot no.slot⟩

structure RoleSites (A : Type*) where
  a : Site A
  b : Site A
  other : Site A
  valid : A

def RoleSites.map (f : A → B) (r : RoleSites A) : RoleSites B :=
  ⟨r.a.map f,r.b.map f,r.other.map f,f r.valid⟩

def roleSites (layout : Bool) (e : Ends A) : RoleSites A :=
  let thick := thickBit o g.toColumns e.source
  let c := Position.select o thick e.target e.source
  let other := Position.select o thick e.source e.target
  let a := toggle o g.toColumns c.site
  let b := forward o g.toColumns d a c.slot
  let good := o.choose thick (o.lit 1)
    (o.choose (thickBit o g.toColumns e.target) (o.lit 1) (o.lit 0) (o.lit 1)) (o.lit 1)
  ⟨a,b,owner o g.toColumns d layout other,good⟩

/-- Compute one rooted occurrence by one call to child enumeration and one edge traversal. -/
def fromChild (layout thin incoming : Bool) (s : Site A) (childSlot u edgeSlot : A) : Ends A :=
  ends o g d incoming (child o g.toColumns d layout thin s childSlot u) edgeSlot

variable (pub : Fin k → Word w) (m : Memory w) (vs : Fin n → Word w)

theorem eval_ends (G : ArcColumns (Term w k n)) (d : ℕ) (incoming : Bool)
    (x : Position (Term w k n)) (i : Term w k n) :
    (ends (terms w k n) G d incoming x i).map (ev pub m vs) =
      ends (words m) (G.map (ev pub m vs)) d incoming (x.map (ev pub m vs)) (ev pub m vs i) := by
  cases incoming <;> simp [ends,Ends.map,Position.map,Site.map,ArcColumns.map,Columns.map,
    forward,backward,terms,words,slot,row,ev]

theorem eval_roleSites (G : ArcColumns (Term w k n)) (d : ℕ) (layout : Bool)
    (e : Ends (Term w k n)) :
    (roleSites (terms w k n) G d layout e).map (ev pub m vs) =
      roleSites (words m) (G.map (ev pub m vs)) d layout (e.map (ev pub m vs)) := by
  cases layout <;>
    simp [roleSites,RoleSites.map,Ends.map,Position.select,Site.select,owner,toggle,
      thickBit,forward,Position.map,Site.map,Columns.map,ArcColumns.map,terms,words,
      Comparison.test,row,slot,ev]

theorem eval_fromChild (G : ArcColumns (Term w k n)) (d : ℕ) (layout thin incoming : Bool)
    (s : Site (Term w k n)) (childSlot u edgeSlot : Term w k n) :
    (fromChild (terms w k n) G d layout thin incoming s childSlot u edgeSlot).map (ev pub m vs) =
      fromChild (words m) (G.map (ev pub m vs)) d layout thin incoming (s.map (ev pub m vs))
        (ev pub m vs childSlot) (ev pub m vs u) (ev pub m vs edgeSlot) := by
  unfold fromChild
  rw [eval_ends,eval_child]
  rfl

end ThreeFlat.Diagonal.CompressorPacking.Native.Placement

end OAI
