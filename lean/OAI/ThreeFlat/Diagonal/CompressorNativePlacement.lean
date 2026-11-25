import OAI.ThreeFlat.RAM.DescriptorExpr

namespace OAI
/-! # Native addressing for owner and child positions in a shrinking step

An old base graph is stored as source-major and destination-major arrays.
The inverse columns contain the original source base, source slot, and
the two XOR shifts of that same arc. A site is stored as three words,
so an address computation never presupposes that the entire old site fits
in the width left for its lane.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Placement
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.DescriptorExpr

open scoped Fin.NatCast
variable {A B : Type*} {w k n : ℕ}

structure Site (A : Type*) where
  base : A
  tag : A
  lane : A
  deriving DecidableEq

structure Position (A : Type*) where
  site : Site A
  bits : A
  slot : A
  deriving DecidableEq

structure Columns (A : Type*) where
  color : A
  offset : A
  dst : A
  forwardTag : A
  forwardLane : A
  src : A
  backSlot : A
  backTag : A
  backLane : A

structure Ops (A : Type*) where
  lit : ℕ → A
  bin : BinaryOp → A → A → A
  load : A → A
  choose : A → A → A → A → A

def terms (w k n : ℕ) : Ops (Term w k n) :=
  ⟨fun x => .literal (x : Word w),.binary,.load,.select .eq⟩

def words (m : Memory w) : Ops (Word w) :=
  ⟨fun x => (x : Word w),BinaryOp.eval,fun a => m a.val,fun a b u v => if a=b then u else v⟩

def Site.map (f : A → B) (s : Site A) : Site B := ⟨f s.base,f s.tag,f s.lane⟩

def Position.map (f : A → B) (x : Position A) : Position B :=
  ⟨x.site.map f,f x.bits,f x.slot⟩

def Columns.map (f : A → B) (c : Columns A) : Columns B :=
  ⟨f c.color,f c.offset,f c.dst,f c.forwardTag,f c.forwardLane,f c.src,
    f c.backSlot,f c.backTag,f c.backLane⟩

variable (o : Ops A) (c : Columns A) (d : ℕ)

def row (base v : A) : A := o.load (o.bin .add base v)

def slot (base v i : A) : A :=
  row o base (o.bin .add (o.bin .mul v (o.lit d)) i)

def thickBit (x : Position A) : A :=
  o.bin .bitAnd (o.bin .shiftRight x.bits (row o c.color x.site.base)) (o.lit 1)

def toggle (s : Site A) : Site A :=
  {s with tag := o.bin .bitXor s.tag (row o c.offset s.base)}

def forward (s : Site A) (i : A) : Site A :=
  ⟨slot o d c.dst s.base i,o.bin .bitXor s.tag (slot o d c.forwardTag s.base i),
    o.bin .bitXor s.lane (slot o d c.forwardLane s.base i)⟩

def backward (s : Site A) (i : A) : Site A :=
  ⟨slot o d c.src s.base i,o.bin .bitXor s.tag (slot o d c.backTag s.base i),
    o.bin .bitXor s.lane (slot o d c.backLane s.base i)⟩

def owner (layout : Bool) (x : Position A) : Site A :=
  let here := x.site
  let shifted := toggle o c here
  let thin := if layout then forward o c d shifted x.slot else shifted
  let flag := thickBit o c x
  ⟨o.choose flag (o.lit 1) here.base thin.base,o.choose flag (o.lit 1) here.tag thin.tag,
    o.choose flag (o.lit 1) here.lane thin.lane⟩

/-- The Boolean specifies the thin block of the ordered child array. -/
def child (layout thin : Bool) (s : Site A) (i u : A) : Position A :=
  if thin then
    let pre := if layout then backward o c d s i else s
    let oldSlot := if layout then slot o d c.backSlot s.base i else i
    ⟨toggle o c pre,u,oldSlot⟩
  else ⟨s,u,i⟩

def admitted (layout thin : Bool) (s : Site A) (i u : A) : A :=
  let x := child o c d layout thin s i u
  o.choose (thickBit o c x) (o.lit 1) (o.lit (if thin then 0 else 1))
    (o.lit (if thin then 1 else 0))

variable (pub : Fin k → Word w) (m : Memory w) (vs : Fin n → Word w)

abbrev ev (z : Term w k n) := z.eval pub m vs

theorem eval_owner (C : Columns (Term w k n)) (d : ℕ) (lay : Bool) (x : Position (Term w k n)) :
    (owner (terms w k n) C d lay x).map (ev pub m vs) =
      owner (words m) (C.map (ev pub m vs)) d lay (x.map (ev pub m vs)) := by
  cases lay <;>
    simp [owner,thickBit,toggle,forward,Site.map,Position.map,Columns.map,terms,words,row,slot,
      Comparison.test,ev]

theorem eval_child (C : Columns (Term w k n)) (d : ℕ) (lay thin : Bool) (s : Site (Term w k n))
    (i u : Term w k n) : (child (terms w k n) C d lay thin s i u).map (ev pub m vs) =
      child (words m) (C.map (ev pub m vs)) d lay thin (s.map (ev pub m vs))
        (ev pub m vs i) (ev pub m vs u) := by
  cases thin <;> cases lay <;>
    simp [child,toggle,backward,Site.map,Position.map,Columns.map,terms,words,row,slot,ev]

theorem eval_admitted (C : Columns (Term w k n)) (d : ℕ) (lay thin : Bool) (s : Site (Term w k n))
    (i u : Term w k n) : ev pub m vs (admitted (terms w k n) C d lay thin s i u) =
      admitted (words m) (C.map (ev pub m vs)) d lay thin (s.map (ev pub m vs))
        (ev pub m vs i) (ev pub m vs u) := by
  cases thin <;> cases lay <;>
    simp [admitted,thickBit,child,toggle,backward,Site.map,Columns.map,terms,words,row,slot,
      Comparison.test,ev]

end ThreeFlat.Diagonal.CompressorPacking.Native.Placement

end OAI
