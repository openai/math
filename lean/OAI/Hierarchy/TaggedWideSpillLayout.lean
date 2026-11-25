import OAI.Hierarchy.TaggedWideDatedLayout
import OAI.Hierarchy.TaggedWideMountedControlFields

namespace OAI
/-! # The physical date sheets for intermediate widths and both halves of a spill -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles RoleProgram
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open SiteControls
open scoped Classical Fin.CommRing BigOperators
variable {T : ℕ}

/-- Role tables use the original numeral at every phase, including the
two pure goods/core layouts with zeroes on every irrelevant physical row. -/
structure SpillDates (T : ℕ) where
  original : Dated T
  middle : Fin T→Expr
  only : Bool→Fin T→Expr
  attempt : Fin T→Bool
  cap : ℕ

variable (z : SpillDates T)
local notation "g" => z.original

def SpillDates.roles (f : Fin 3) : Dated T :=
  { z.original with
    amount := Fin.cases (.lit 0) (fun j => if f = 0 then z.middle j else z.only (decide (f = 2)) j) }

def SpillDates.roleRoot (start : ℕ) (f : Fin 3) :=
  start+f.val*((T+1)*(3*(g).roleSpan))

def SpillDates.dateRole (start : ℕ) (j : Fin T) (f : Fin 3) :=
  (g).roleStart (z.roleRoot start f) j.succ

/-- Date zero of each auxiliary table is only the zero-width sentinel.
The table at j+1 records the material of event j. -/
def SpillDates.roleSheet (rom start : ℕ) (t : Fin (3*((T+1)*3))) : Scatter :=
  let stage : Fin 3×Fin ((T+1)*3):=finProdFinEquiv.symm t
  let date : Fin (T+1)×Fin 3:=finProdFinEquiv.symm stage.2
  (z.roles stage.1).rolePage rom (z.roleRoot start stage.1) date.1 date.2

def SpillDates.ballot (rom oldWork start : ℕ) (j : Fin T) : Scatter :=
  let root:=z.roleRoot start 2
  ((g).ballot j).sheet (g).sites ((g).ballotROM rom j) ((g).ballotStart root j)
    ((g).fields j ((g).siteROM rom) ((g).siteStride rom) ((g).roleStart oldWork j.castSucc) (z.dateRole start j 0))

def SpillDates.packetControl (rom oldWork start : ℕ) (j : Fin T) : Scatter :=
  let root:=z.roleRoot start 2
  ((g).control j).sheet (g).sites ((g).controlROM rom j) ((g).controlBase root j)
    ((g).controls j ((g).siteStride rom) ((g).roleStart oldWork j.castSucc) (z.dateRole start j 0)
      ((g).ballotStart root j+1))

def SpillDates.preClip (oldWork start : ℕ) (j : Fin T) :=
  if z.attempt j then z.dateRole start j 0 else (g).roleStart oldWork j.castSucc

def spillLow {D : ℕ} (whole only : Fin D→LocalPrefix.Columns) (q : Fin D) : Expr :=
  LocalPrefix.total D (fun i=>weight (only i) (whole q))

def spillControls (sites n D cap : ℕ) (table : Bank) (pre post left right : ℕ) :
    Fields (⟨sites,1,fieldCount D⟩ : Shape) where
  selected := fun _=>.lit 1
  site := fun _=>.row
  value _ f :=
    let row (b : Bool) := columns (D:=D) n (if b then post else pre) sites
      (ProtocolRAMPurchaseSampler.bits (sites*D)) table .row
    let clipped (b : Bool) := columns (D:=D) n (if b then right else left) sites
      (ProtocolRAMPurchaseSampler.bits (sites*D)) table .row
    compile cap row (fun b=>spillLow (row b) (clipped b)) ((fieldNumber D).symm f)

def SpillDates.spillStart (start : ℕ) (j : Fin T) :=
  offset ((g).maskStart (z.roleRoot start 2)) (fun i=>((g).control i).span (g).sites) j

def SpillDates.spillControl (rom oldWork start : ℕ) (j : Fin T)
    (count : ∀i,(g).controlColumns i=fieldCount (g).roleCount) : Scatter :=
  let p:=(g).control j
  let site:=spillControls (g).sites (g).physical (g).roleCount z.cap ((g).siteStride rom) (z.preClip oldWork start j)
    ((g).roleStart oldWork j.succ) (z.dateRole start j 1) (z.dateRole start j 2)
  p.sheet (g).sites ((g).controlROM rom j) (z.spillStart start j)
    ⟨site.selected,site.site,fun i f=>site.value i (f.cast (count j))⟩

def SpillDates.endAt (start : ℕ) :=
  endOf ((g).maskStart (z.roleRoot start 2)) (fun i=>((g).control i).span (g).sites)

def SpillDates.last (T : ℕ) := (3*((T+1)*3)-1)+(T+(T+T))

def SpillDates.sheets (rom oldWork start : ℕ) (count : ∀i,(g).controlColumns i=fieldCount (g).roleCount) :
    Fin (last T+1)→Scatter :=
  (Fin.addCases (z.roleSheet rom start)
    (Fin.addCases (z.ballot rom oldWork start)
      (Fin.addCases (z.packetControl rom oldWork start) (fun j=>z.spillControl rom oldWork start j count)))) ∘
    Fin.cast (by dsimp [last];omega)

def SpillDates.program (W rom oldWork start : ℕ) (count : ∀i,(g).controlColumns i=fieldCount (g).roleCount) :=
  ProcedureBank.program (last T) (fun i=>(z.sheets rom oldWork start count i).code W)

def SpillDates.ticks (rom oldWork start : ℕ) (count : ∀i,(g).controlColumns i=fieldCount (g).roleCount) :=
  ∑i,(z.sheets rom oldWork start count i).ticks

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
