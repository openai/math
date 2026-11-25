import OAI.ThreeFlat.Diagonal.PhysicalNodeBankLayout
import OAI.ThreeFlat.RAM.NavigationNodeRowProgram
import OAI.ThreeFlat.Diagonal.NavigationScalar
import OAI.ThreeFlat.Diagonal.NavigationCountedLoop

namespace OAI
/-! # Native code for directory compaction and the counted node row publisher -/
namespace ThreeFlat.Diagonal.NavigationPass.TraceNodeHeaders
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows PhysicalPinsExpr PhysicalProcedure
open scoped Fin.CommRing Classical

abbrev E := Formula 1

/-- Select the physical field at the current destination offset. -/
def pick (index : E) : ℕ → List E → E
  | _, [] => .lit 0
  | j, x::xs => .select .eq index (.lit j) x (pick index (j+1) xs)

/-- Each iteration emits one compact word. The current and preceding physical headers
supply the forward parent pointer and the selected site's own data pointers. -/
def compactRow (ctrl : ℕ) : E :=
  let fld (j : ℕ) := MotifRows.field (.load (.lit ctrl)) j
  let i := Formula.cut (.reg 0) (fld 0)
  let t := Formula.op .div i (.lit 16)
  let j := Formula.op .mod i (.lit 16)
  let tab (time : E) (off : ℕ) := MotifRows.field (.op .add (fld 2) (.op .mul (.lit 64) time)) off
  let prev := tab (.cut t (.lit 1))
  let cur := tab t
  let prior (seed : ℕ) (live : E) := Formula.select .eq t (.lit 0) (fld seed) live
  let parent (x : E) := Formula.select .lt t (fld 3) x (.lit 0)
  let afterCount := Formula.op .div (prev 35) (.lit 5)
  let first := prior 6 (.op .add (prev 6) (prev 5))
  let count := prior 7 afterCount
  let kind := prior 8 (.select .eq (prev 33) (.lit 1) (.lit 1) (.lit 2))
  let arity := prior 9 (.select .eq (prev 33) (.lit 1) (.op .div (prev 5) afterCount) (.lit 1))
  pick j 0
    [.op .add (fld 4) (.op .mul (.lit 2) first),
     .op .mul (.lit 2) count,
     .op .add (fld 5) (.op .mul (.lit 8) first),
     .op .mul (.lit 8) count,
     .op .add (fld 0) (.op .mul (.lit 16) (.op .add t (.lit 1))),
     first, kind, arity, prior 10 (prev 42), prior 11 (prev 34), prior 12 (prev 38),
     .select .lt t (fld 3) (.lit 0) (.lit 1),
     parent (.op .add (cur 6) (cur 5)), parent (cur 44)]

def compactScan (W ctrl : ℕ) : Procedure W :=
  HeaderScan.procedure (ctrl : Word W) 0 1 (HeaderScan.closed (compactRow ctrl))

end ThreeFlat.Diagonal.NavigationPass.TraceNodeHeaders

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure TraceNodeHeaders
open scoped Fin.CommRing
noncomputable section
def compactPublish (W ctrl : ℕ) (a : NodeArchive) (n : ℕ) : Procedure W :=
  (compactScan W ctrl).seq
    ((start (a.banks.current:Word W) a.headerBase).seq ((start (a.counter:Word W) n).seq
      (loop (a.counter:Word W) (NavigationNodeRows.procedure a.banks a.childCap a.halfCap a.motifCap))))


def compactTicks (ctrl n budget : ℕ) :=
  (11 + 16*n*(2*(compactRow ctrl).work+4)) + (3 + (3 + (n*(7+budget)+4)))

end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
