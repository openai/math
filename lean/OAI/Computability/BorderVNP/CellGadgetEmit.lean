import OAI.Computability.BorderVNP.CellFactorEmit
import OAI.Computability.BorderVNP.CellLocalSweep
import OAI.Computability.BorderVNP.CellEmitBoxCounts
import OAI.Computability.BorderVNP.CellLocalFinish
import OAI.Computability.BorderVNP.CellGadgetRows

/-! # Compiling all reported gadget subtotals on the private bit stacks

Each report visits all box factors in their physical order, checks the resulting
prefix-count rectangle, and consumes the rectangle before the next report.
The finite compiler only materializes a single body per repeated copy loop.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

variable {α : Type} {ea : α → List Bool}
variable {dir : α → Directory} {label : α → ℕ} {bits : α → List ℕ}

/-- Fixed binary scalar procedure for the local prefix rectangle size. -/
noncomputable def gadgetRectangle : Procedure Nat.bits Nat.bits (fun n => (n+1)*(n+1)) :=
  Procedure.binaryMul.comp ((prefixSucc (Procedure.identity Nat.bits)).pair
    (prefixSucc (Procedure.identity Nat.bits)))

/-- Fixed initialization printer on the binary cap alone. -/
noncomputable def gadgetInit : Statement Nat.bits (fun n => Prefix.initGen 0 n) :=
  prefixInit (Procedure.constant Nat.bits Nat.bits 0) (Procedure.identity Nat.bits)

private noncomputable def rectangle {cap : α → ℕ} (hc : Procedure ea Nat.bits cap) :
    Procedure ea Nat.bits (fun x => (cap x+1)*(cap x+1)) :=
  gadgetRectangle.comp hc

/-- Emit the initialization, all globally indexed transitions, and the terminal
candidate test for one original reported subtotal. -/
noncomputable def gadgetCheckerStmt (hd : Procedure ea Typed.directory dir)
    (hi : Procedure ea Nat.bits label) (hs : Procedure ea Typed.naturals bits) :
    Statement ea (fun x => Gadget.checker (dir x) (label x) (bits x)) := by
  let cap := getVisitCount.comp hd
  let aux := rectangle cap
  let zero := Procedure.constant ea Nat.bits 0
  let sweep := Local.sweepStmt .gadget hd (cap.pair (aux.pair hi))
  exact seqStmt (gadgetInit.comp cap) (seqStmt sweep (Finish.localStmt zero aux cap hs))

/-- Emit one subtotal check inside its unique local flag rectangle. -/
noncomputable def gadgetRowStmt (hd : Procedure ea Typed.directory dir)
    (hi : Procedure ea Nat.bits label) (hs : Procedure ea Typed.naturals bits) :
    Statement ea (fun x => Gadget.row (dir x) (label x) (bits x)) :=
  scopedFlags (rectangle (getVisitCount.comp hd)) (gadgetCheckerStmt hd hi hs)

/-- Emit each report in the original list order, using its zero-based position
as the gadget identifier and its actual binary count wires. -/
noncomputable def subtotalGuardsStmt (hd : Procedure ea Typed.directory dir) :
    Statement ea (fun x => (dir x).subtotalGuards) := by
  let env := Procedure.first ea (prodCode Nat.bits Typed.naturals)
  let entry := Procedure.second ea (prodCode Nat.bits Typed.naturals)
  let i := (Procedure.first Nat.bits Typed.naturals).comp entry
  let wires := (Procedure.second Nat.bits Typed.naturals).comp entry
  let row := gadgetRowStmt (hd.comp env) i wires
  exact sequenceMapIdx (f := fun x i bs => Gadget.row (dir x) i bs) [] (getReports.comp hd) row

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
