import OAI.ThreeFlat.Diagonal.CompressorDemandReader
import OAI.ThreeFlat.Diagonal.CompressorNativeGraph
import OAI.ThreeFlat.Diagonal.ShrinkLayout

namespace OAI
/-! # Shrinking width writer at physical outgoing slot/lane addresses

The native slot sweep also supplies its elected one-based rooted identifier
as `Graph.Field.identifier`. Divide it back into the original source base,
tag, port, word and consumed-port digits. Translating the root by the
requested physical output lane recovers its individual histogram row.
A zero identifier is the deterministic padding row.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
variable {n : ℕ}
abbrev F (n : ℕ) := Formula n

def choose4 (k : F n) (f : Fin 4 → F n) : F n :=
  .select .eq k (.lit 0) (f 0) (.select .eq k (.lit 1) (f 1) (.select .eq k (.lit 2) (f 2) (f 3)))

structure Cursor (A : Type*) where
  old : Position A
  oldPort : A
  survivor : A
  copy : A

/-- Inverse to the mixed-radix physical rooted-edge key. -/
def decode (S : Graph.Stage) (tagCount id : F n) : Cursor (F n) :=
  let code := Formula.cut id (.lit 1)
  let copy := Formula.op .mod code (.lit S.pieceRadix)
  let withType := Formula.op .div code (.lit S.pieceRadix)
  let kind := Formula.op .mod withType (.lit 4)
  let withLabel := Formula.op .div withType (.lit 4)
  let label := Formula.op .mod withLabel (.lit S.degree)
  let withBits := Formula.op .div withLabel (.lit S.degree)
  let bits := Formula.op .mod withBits (.lit (2^S.colors))
  let withPort := Formula.op .div withBits (.lit (2^S.colors))
  let port := Formula.op .mod withPort (.lit S.degree)
  let withTag := Formula.op .div withPort (.lit S.degree)
  ⟨⟨⟨.op .div withTag tagCount,.op .mod withTag tagCount,.lit 0⟩,bits,label⟩,port,kind,copy⟩

/-- Translate a rooted motif so that its chosen source role occupies lane k. -/
def unroot (g : ArcColumns (F n)) (S : Graph.Stage) (layout : Bool) (a : Cursor (F n))
    (lane : F n) : Position (F n) :=
  let o := Demand.formulaOps n
  let e := ends o g S.degree false a.old a.oldPort
  let s := roleSites o g S.degree layout e
  let atSource := choose4 a.survivor fun i => (Graph.siteAt s (Graph.roles layout i).1).lane
  {a.old with site := {a.old.site with lane := .op .bitXor atSource lane}}

def lowerCD (g : ArcColumns (F n)) (p : Demand.WidthLayout n) (a : Position (F n)) (port : F n) : F n :=
  let o := Demand.formulaOps n
  RAM.MotifRows.totals ((List.finRange (2^p.colors)).map fun u =>
    let x := {a with bits := Formula.lit u.val}
    let e := ends o g p.degree false x port
    let cd := o.choose (thickBit o g.toColumns x) (.lit 1)
      (o.choose (thickBit o g.toColumns e.target) (.lit 1) (.lit 0) (.lit 1)) (.lit 1)
    .select .lt (.lit u.val) a.bits cd (.lit 0))

/-- Global dense row, stripping the low color digit from the old physical ordinal
and counting just the preceding CD incidences in that final block. -/
def motifRow (g : ArcColumns (F n)) (p : Demand.WidthLayout n) (x : Position (F n)) (port : F n) : F n :=
  let block := Formula.op .div (Demand.physical p x port) (.lit (2^p.colors))
  .op .add (.op .mul block (.lit (3*2^(p.colors-2)))) (lowerCD g p x port)

def output (g : ArcColumns (F n)) (p : Demand.WidthLayout n) (S : Graph.Stage) (layout : Bool)
    (keys widths remaining index : F n) : F n :=
  let slot := Formula.op .div index remaining
  let lane := Formula.op .mod index remaining
  let id := Formula.load (.op .add keys slot)
  let a := decode S p.tagCount id
  let x := unroot g S layout a lane
  let row := motifRow g p x a.oldPort
  let retained := choose4 a.survivor fun i => .lit (ShrinkMotif.survivor layout i).val
  let address := Formula.op .add widths (.op .add (.op .mul row (.lit 8)) retained)
  let piece := choose4 a.survivor fun i => Demand.balanced (.load address) (S.pieces i) a.copy
  .select .eq id (.lit 0) (.lit 0) piece

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth

end OAI
