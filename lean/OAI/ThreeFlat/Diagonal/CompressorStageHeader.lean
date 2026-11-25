import OAI.ThreeFlat.Diagonal.CompressorDemandInput
import OAI.ThreeFlat.Diagonal.CompressorNativeTags
import OAI.ThreeFlat.Diagonal.CompressorStageMachine

namespace OAI
/-! # Shrinking-stage row subroutines at the chronological header ABI

The constants are header offsets in words. Field zero is the number of
global CD motifs. The old and successor graph arrays have six equal
columns in source and destination order: neighbor, mate, displacement.
The auxiliary source identifier is a separate single column.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement
open scoped Fin.NatCast
variable {A : Type*} {w : ℕ}

abbrev motifRows := 0
abbrev countTable := 1
abbrev choiceTable := 2
abbrev issued := 3
abbrev nextInfo := 4
abbrev inputSites := 5
abbrev firstNode := 6
abbrev demand := 8
abbrev demandWords := 9
abbrev oldBases := 10
abbrev oldGraph := 11
abbrev oldSlots := 12
abbrev oldWidths := 13
abbrev remaining := 14
abbrev tags := 15
abbrev splitShifts := 16
abbrev splitWords := 17
abbrev colors := 18
abbrev offsets := 19
abbrev nextGraph := 20
abbrev graphWords := 21
abbrev nextSlots := 22
abbrev keys := 23
abbrev nextWidths := 24
abbrev widthWords := 25
abbrev oldLanes := 26
abbrev selected := 27

def atField (o : Ops A) (current : A) (i : ℕ) : A := o.load (o.bin .add (o.load current) (o.lit i))

def column (o : Ops A) (origin size : A) (i : ℕ) : A :=
  o.bin .add origin (o.bin .mul size (o.lit i))

def oldColumns (o : Ops A) (current : A) : ArcColumns A :=
  let f := atField o current
  let raw := column o (f oldGraph) (f oldSlots)
  let sliced := column o (f splitShifts) (f oldSlots)
  ⟨⟨f colors,f offsets,raw 0,sliced 2,sliced 3,raw 3,raw 4,sliced 6,sliced 7⟩,
    sliced 0,sliced 1,sliced 4,sliced 5⟩

def splitRow (o : Ops A) (current addr : A) (c d : ℕ) : A :=
  let f := atField o current
  let len := f oldSlots
  let pos := o.bin .sub addr (f splitShifts)
  let i := o.bin .mod pos len
  let field := o.bin .div pos len
  let raw (j : ℕ) := o.load (o.bin .add (column o (f oldGraph) len j) i)
  let v := o.choose (o.bin .div field (o.lit 4)) (o.lit 0) (raw 2) (raw 5)
  let kind := o.bin .mod field (o.lit 4)
  let left := o.bin .div v (o.lit (2^c))
  let high := o.bin .div left (o.lit d)
  o.choose kind (o.lit 0) (o.bin .mod v (o.lit (2^c)))
    (o.choose kind (o.lit 1) (o.bin .mod left (o.lit d))
      (o.choose kind (o.lit 2) (o.bin .mod high (f tags)) (o.bin .div high (f tags))))

abbrev T (w : ℕ) := Term w 1 1
def termOps (w : ℕ) := terms w 1 1
def termField (current : Word w) := atField (termOps w) (.literal current)

def color (current : Word w) (d : ℕ) : T w :=
  let f := termField current
  let raw := column (termOps w) (f oldGraph) (f oldSlots)
  colorRow d (f colors) (raw 0) (raw 3)

def tag (current : Word w) (d t : ℕ) : T w :=
  let f := termField current
  let g := oldColumns (termOps w) (.literal current)
  offsetRow ⟨f offsets,g.dst,g.src,g.forwardTag,g.backTag⟩ d t

def radices (o : Ops A) (current : A) (S : Graph.Stage) : Radices A :=
  ⟨atField o current tags,atField o current remaining,o.lit (2^S.colors),o.lit S.degree⟩

def widthLayout (current : Formula 1) (S : Graph.Stage) : Demand.WidthLayout 1 :=
  let f := atField (Demand.formulaOps 1) current
  ⟨f oldWidths,f oldLanes,f tags,S.degree,S.colors⟩

def input (current : Word w) (S : Graph.Stage) : T w :=
  let o := Demand.formulaOps 1
  let ptr := Formula.lit current.val
  let f := atField o ptr
  (ShrinkWidth.inputPair (oldColumns o ptr) (widthLayout ptr S) (f remaining)
    (.cut (.reg 0) (f demand))).compile (fun _ => 0)

def graph (current : Word w) (S : Graph.Stage) (ident : Bool) : T w :=
  let o := termOps w
  let ptr := Term.literal current
  let f := termField current
  let g := oldColumns o ptr
  let r := radices o ptr S
  let make (layout : Bool) : T w := if ident then Graph.updateRow g r S layout false .identifier (f keys) (o.lit 1)
    else shrinkColumns g r S layout (f nextGraph) (f nextSlots) (o.lit 1)
  o.choose (f selected) (o.lit 1) (make true) (make false)

def output (current : Word w) (S : Graph.Stage) : T w :=
  let o := Demand.formulaOps 1
  let ptr := Formula.lit current.val
  let f := atField o ptr
  let make (layout : Bool) := ShrinkWidth.output (oldColumns o ptr) (widthLayout ptr S) S layout
    (f keys) (f issued) (f remaining) (.cut (.reg 0) (f nextWidths))
  (Formula.select .eq (f selected) (.lit 1) (make true) (make false)).compile (fun _ => 0)

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
