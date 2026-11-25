import OAI.ThreeFlat.Diagonal.CompressorNodeChildren
import OAI.ThreeFlat.Diagonal.CompressorNodeHalves

namespace OAI
/-! # Bit origins of selected old demands and new supply pieces

A selected AB slice can cross several old physical wires. Each positive-width
old interval occupies consecutive positions in order of its physical source
address. An address descriptor locates the individual bit before converting
the endpoint to a child ordinal and an outgoing or incoming half slot.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

open RAM.PhysicalPinsExpr Placement

variable {n : ℕ}
abbrev F (n : ℕ) := Formula n

/-- Scope, child number, half number, bit number. For scope 3 the three
data words are the absorbed motif-edge number, bit number, and zero. -/
abbrev Address (n : ℕ) := Fin 4 → F n

def empty : Address n := fun _ => .lit 0

def select (test : F n) (yes no : Address n) : Address n := fun i =>
  .select .eq test (.lit 1) (yes i) (no i)

def layout (ptr : F n) (S : Graph.Stage) : Demand.WidthLayout n :=
  let f := atField (Demand.formulaOps n) ptr
  ⟨f oldWidths,f oldLanes,f tags,S.degree,S.colors⟩

/-- Absolute old source arc number, as written into local incident row word 0. -/
def oldArc (ptr : F n) (S : Graph.Stage) (key : F n) : Ends (F n) :=
  let o := Demand.formulaOps n
  let p := layout ptr S
  let f := atField o ptr
  let (x,port) := ShrinkWidth.upperSource p (f remaining) (.op .div key (.lit (2^S.colors)))
  let src : Position (F n) := {x with bits := .op .mod key (.lit (2^S.colors))}
  ends o (oldColumns o ptr) S.degree false src port

def mate (ptr : F n) (S : Graph.Stage) (v i : F n) : F n :=
  let o := Demand.formulaOps n
  let f := atField o ptr
  slot o S.degree (column o (f oldGraph) (f oldSlots) 1) v i

/-- Inverse of the ordered child array. Remove the fixed color bit. In the
thin block of layout 1, the child is indexed by the arrival slot. -/
def childNumber (ptr : F n) (S : Graph.Stage) (lay : Bool) (x : Position (F n)) : F n :=
  let o := Demand.formulaOps n
  let g := (oldColumns o ptr).toColumns
  let step := Formula.op .shiftLeft (.lit 1) (row o g.color x.site.base)
  let hi := Formula.op .div x.bits (.op .mul (.lit 2) step)
  let free := Formula.op .add (.op .mod x.bits step) (.op .mul step hi)
  let i := if lay then mate ptr S x.site.base x.slot else x.slot
  let slotIndex := o.choose (thickBit o g x) (.lit 1) x.slot (.op .add (.lit S.degree) i)
  .op .add (.op .mul slotIndex (.lit (2^(S.colors-1)))) free

def oldHalf (ptr : F n) (S : Graph.Stage) (lay : Bool)
    (e : Ends (F n)) (incoming j : F n) : Address n :=
  let o := Demand.formulaOps n
  let x := Position.select o incoming e.target e.source
  let half := o.choose incoming (.lit 1)
    (.op .add (.lit S.degree) (mate ptr S e.source.site.base e.originalSlot)) e.originalSlot
  ![.lit 1,childNumber ptr S lay x,half,j]

/-- Select from ordered variable-size blocks, including empty ones. The
callback receives the local bit position in a positive-width block. -/
def locate (blocks : List (F n × (F n → Address n))) (j : F n) : Address n :=
  match blocks with
  | [] => empty
  | (len,resolve) :: tail => fun k =>
    .select .lt j len (resolve j k) (locate tail (.cut j len) k)

def startPiece (total : F n) (count : ℕ) (i : F n) : F n :=
  let q := Formula.op .div total (.lit count)
  let r := Formula.op .mod total (.lit count)
  .op .add (.op .mul i q) (.select .lt i r i r)

def thickBlocks (ptr : F n) (S : Graph.Stage) (lay : Bool)
    (v : Site (F n)) (port incoming : F n) : List (F n × (F n → Address n)) :=
  let o := Demand.formulaOps n
  let g := oldColumns o ptr
  let p := layout ptr S
  (List.finRange S.degree).flatMap fun h => (List.finRange (2^S.colors)).map fun u =>
    let x : Position (F n) := ⟨v,.lit u.val,.lit h.val⟩
    let len := Demand.element g p v port h u
    let arc := ends o g S.degree false x port
    (len, oldHalf ptr S lay arc incoming)

def demandAddress (ptr : F n) (S : Graph.Stage) (lay : Bool)
    (e : Ends (F n)) (party edge j : F n) : Address n :=
  let o := Demand.formulaOps n
  let g := oldColumns o ptr
  let p := layout ptr S
  let thick := thickBit o g.toColumns e.source
  let c := Position.select o thick e.target e.source
  let a := toggle o g.toColumns c.site
  let key := Demand.physical p e.source e.originalSlot
  let Q := 3*(2^S.colors*S.degree)/4
  let total := Demand.thickWidth g p a c.slot
  let start := startPiece total Q (Demand.bundleNumber g p a c.slot key)
  let ab := locate (thickBlocks ptr S lay a c.slot party) (.op .add start j)
  let inCD := o.choose party (.lit 2) thick (.op .bitXor thick (.lit 1))
  let cd := oldHalf ptr S lay e inCD j
  fun k => .select .eq edge (.lit 0) (.select .lt party (.lit 2) (ab k) (.lit 0))
    (.select .eq edge (.lit 1) (.select .eq party (.lit 2) (cd k)
      (.select .eq party (.lit 3) (cd k) (.lit 0))) (.lit 0))

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
