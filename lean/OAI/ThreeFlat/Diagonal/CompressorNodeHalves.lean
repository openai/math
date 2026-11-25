import OAI.ThreeFlat.Diagonal.CompressorStageHeader

namespace OAI
/-! # Word-indexed successor half records

The successor first lists the outgoing halves in slot order, then the
incoming halves. For an incoming half the reverse columns recover the old
source slot and translate the destination lane by the recorded XOR shift.
The half-bit prefix is the sum of all earlier widths at that site.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Halves
open RAM.PhysicalPinsExpr
abbrev F := Formula 1

structure Half where
  edge : F
  side : F
  width : F

structure HalfColumns where
  remaining : F
  nextGraph : F
  nextSlots : F
  nextWidths : F

def shrinkColumns (current : F) : HalfColumns :=
  let f := atField (Demand.formulaOps 1) current
  ⟨f ShrinkStage.remaining,f ShrinkStage.nextGraph,f ShrinkStage.nextSlots,f ShrinkStage.nextWidths⟩

def half (q : HalfColumns) (D : ℕ) (site h : F) : Half :=
  let lane := Formula.op .mod site q.remaining
  let base := Formula.op .div site q.remaining
  let port := Formula.op .mod h (.lit D)
  let slotRow := Formula.op .add (.op .mul base (.lit D)) port
  let read (col : ℕ) := Formula.load (.op .add (column (Demand.formulaOps 1) q.nextGraph q.nextSlots col) slotRow)
  let sameSlot := Formula.op .add (.op .mul slotRow q.remaining) lane
  let source := Formula.op .add (.op .mul (read 3) (.lit D)) (read 4)
  let remote := Formula.op .add (.op .mul source q.remaining) (.op .bitXor lane (read 5))
  let ix := Formula.select .lt h (.lit D) sameSlot remote
  ⟨ix,.select .lt h (.lit D) (.lit 0) (.lit 1),.load (.op .add q.nextWidths ix)⟩

def «prefix» (q : HalfColumns) (D : ℕ) (site h : F) : F :=
  RAM.MotifRows.totals ((List.finRange (2*D)).map fun i =>
    .select .lt (.lit i.val) h (half q D site (.lit i.val)).width (.lit 0))

def field (q : HalfColumns) (D : ℕ) (site h j : F) : F :=
  let p := half q D site h
  .select .eq j (.lit 0) p.edge (.select .eq j (.lit 1) p.side
    (.select .eq j (.lit 2) p.width («prefix» q D site h)))

/-- For each site, a fixed block of `2*D` successive four-word rows. -/
def record (q : HalfColumns) (D : ℕ) (linear : F) : F :=
  let row := Formula.op .div linear (.lit 4)
  field q D (.op .div row (.lit (2*D))) (.op .mod row (.lit (2*D))) (.op .mod linear (.lit 4))

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Halves

end OAI
