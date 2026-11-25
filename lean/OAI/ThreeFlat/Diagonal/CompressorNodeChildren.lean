import OAI.ThreeFlat.Diagonal.CompressorNodeIncident

namespace OAI
/-! # Direct physical child and owner ordinals in a shrinking stage -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.ChildRows
open RAM.PhysicalPinsExpr Placement
abbrev F := Formula 1

def unpackOld (current : F) (S : Graph.Stage) (i : F) : Position F :=
  let f := atField (Demand.formulaOps 1) current
  let b := Formula.op .div i (f oldLanes)
  let z := Formula.op .mod i (f oldLanes)
  let low := Formula.op .div z (.lit (2^S.colors))
  let high := Formula.op .div low (.lit S.degree)
  ⟨⟨b,.op .mod high (f tags),.op .div high (f tags)⟩,.op .mod z (.lit (2^S.colors)),.op .mod low (.lit S.degree)⟩

def packOld (current : F) (S : Graph.Stage) (x : Position F) : F :=
  let f := atField (Demand.formulaOps 1) current
  let hi := Formula.op .add x.site.tag (.op .mul (f tags) x.site.lane)
  let mid := Formula.op .add x.slot (.op .mul (.lit S.degree) hi)
  let lo := Formula.op .add x.bits (.op .mul (.lit (2^S.colors)) mid)
  .op .add (.op .mul x.site.base (f oldLanes)) lo

def packNew (current : F) (v : Site F) : F :=
  let f := atField (Demand.formulaOps 1) current
  let b := Formula.op .add (.op .mul v.base (f tags)) v.tag
  .op .add (.op .mul b (f remaining)) v.lane

def parent (current : F) (S : Graph.Stage) (layout : Bool) (old : F) : F :=
  let o := Demand.formulaOps 1
  let v := owner o (oldColumns o current).toColumns S.degree layout (unpackOld current S old)
  packNew current v

/-- Insert a prescribed bit at the old base color. The free bits below
and above that color stay in their original little-endian positions. -/
def insert (u color : F) (thin : Bool) : F :=
  let step := Formula.op .shiftLeft (.lit 1) color
  let low := Formula.op .mod u step
  let high := Formula.op .mul (.op .div u step) (.op .mul (.lit 2) step)
  if thin then .op .add high low else .op .add high (.op .add step low)

def childValue (current : F) (S : Graph.Stage) (layout thin : Bool)
    (v : Site F) (i u : F) : F :=
  let o := Demand.formulaOps 1
  let g := (oldColumns o current).toColumns
  let x := child o g S.degree layout thin v i (.lit 0)
  let bits := insert u (row o g.color x.site.base) thin
  packOld current S {x with bits}

/-- One absolute child node identifier for each slot in the contiguous
per-parent list. `firstNode` is the first global identifier of the old layer. -/
def entry (current : F) (S : Graph.Stage) (layout : Bool) (linear : F) : F :=
  let f := atField (Demand.formulaOps 1) current
  let cap := S.degree*2^S.colors
  let free := 2^(S.colors-1)
  let v := Incidents.siteAt current (.op .div linear (.lit cap))
  let i := Formula.op .mod linear (.lit cap)
  let n := Formula.op .div i (.lit free)
  let slot := Formula.op .mod n (.lit S.degree)
  let u := Formula.op .mod i (.lit free)
  let value := Formula.select .lt n (.lit S.degree) (childValue current S layout false v slot u)
    (childValue current S layout true v slot u)
  .op .add (f firstNode) value

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.ChildRows

end OAI
