import OAI.Hierarchy.TaggedWideBallotShape
import OAI.Hierarchy.TaggedWideScatter
import OAI.Hierarchy.TaggedWideDatedEmitters
import OAI.Hierarchy.TaggedWideSiteReplay

namespace OAI
/-! # Fixed addresses of the history, elected-party and local comparison pages -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open ProbeStage.CoreBoard.HistoryRoles RoleProgram
open scoped BigOperators Classical Fin.CommRing

def Shape.sheet (p : Shape) (sites rom work : ℕ) (x : Fields p) : Scatter :=
  let width := sites*p.columns
  let val := SiteScatter.selectedValue (I:=p.candidates) rom x.selected x.value
  let stride := RoleROM.bank (rom+3*p.count) sites
  let index := SiteScatter.fieldIndex (I:=p.candidates) (C:=p.columns) rom stride x.site
  ⟨work+1,width,work+1+width,p.count,RoleWidths.destination (work+1) work val index,val⟩

/-- All sheets read the same original stock/geometry banks and use the actual addresses
of preceding dated sheets when they inspect a stored peer, candidate or turn field. -/
structure Dated (T : ℕ) where
  sites : ℕ
  physical : ℕ
  roleCount : ℕ
  chart : Chart
  sockets : Bool → Socket
  siteDirectorySize : ℕ
  amount : Fin (T+1) → Expr
  ordinal : Expr
  ballot : Fin T → Shape
  controlColumns : Fin T → ℕ
  fields : ∀j,ℕ→Bank→ℕ→ℕ→Fields (ballot j)
  controls : ∀j,Bank→ℕ→ℕ→ℕ→Fields (⟨sites,1,controlColumns j⟩ : Shape)
  rawEdges : ℕ
  measured : Bank
  lanes : ℕ
  orderedSlot : Bool → Expr

variable {T : ℕ} (p : Dated T)

def Dated.control (j : Fin T) : Shape := ⟨p.sites,1,p.controlColumns j⟩
def Dated.roleWords := p.sites*p.roleCount
def Dated.roleSpan := DatedRoleSheets.span p.roleWords p.physical
def Dated.roleStart (work : ℕ) (j : Fin (T+1)) := work+j.val*(3*p.roleSpan)
def Dated.rolesEnd (work : ℕ) := work+(T+1)*(3*p.roleSpan)

def Dated.siteStride (rom : ℕ) := RoleROM.bank rom p.sites
def Dated.siteROM (rom : ℕ) := rom+p.sites
def Dated.firstROM (rom : ℕ) := p.siteROM rom+p.siteDirectorySize

def Dated.rolePage (rom work : ℕ) (j : Fin (T+1)) (f : Fin 3) : Scatter :=
  let start := p.roleStart work j
  let size := p.amount j
  let base := DatedRoleSheets.sheet start p.roleWords p.physical f
  ⟨base,p.roleWords,base+p.roleWords,p.physical+p.physical,
    DatedRoleSheets.dest p.physical p.chart p.sockets (p.siteStride rom) size p.ordinal start p.roleWords f,
    DatedRoleSheets.word p.physical p.chart p.sockets size p.ordinal f⟩

/-- The two public tables are allocated before the first mutable date. Every date may
share the finite constant bounding its shape. Addresses therefore use an arithmetic
stride with no dynamic pointer or input-dependent placement. -/
def stride {T : ℕ} (sizes : Fin T→ℕ) := ∑j,sizes j
def offset {T : ℕ} (base : ℕ) (sizes : Fin T→ℕ) (j : Fin T) := base+j.val*stride sizes
def endOf {T : ℕ} (base : ℕ) (sizes : Fin T→ℕ) := base+T*stride sizes

def Dated.ballotROM (rom : ℕ) (j : Fin T) := offset (p.firstROM rom) (fun j=>(p.ballot j).advice p.sites) j
def Dated.controlROMStart (rom : ℕ) := endOf (p.firstROM rom) (fun j=>(p.ballot j).advice p.sites)
def Dated.controlROM (rom : ℕ) (j : Fin T) := offset (p.controlROMStart rom) (fun j=>(p.control j).advice p.sites) j
def Dated.maskROM (rom : ℕ) := endOf (p.controlROMStart rom) (fun j=>(p.control j).advice p.sites)
def Dated.romEnd (rom : ℕ) := p.maskROM rom+p.rawEdges
def Dated.ballotStart (work : ℕ) (j : Fin T) := offset (p.rolesEnd work) (fun j=>(p.ballot j).span p.sites) j
def Dated.controlStart (work : ℕ) := endOf (p.rolesEnd work) (fun j=>(p.ballot j).span p.sites)
def Dated.controlBase (work : ℕ) (j : Fin T) := offset (p.controlStart work) (fun j=>(p.control j).span p.sites) j
def Dated.maskStart (work : ℕ) := endOf (p.controlStart work) (fun j=>(p.control j).span p.sites)
def Dated.stageWidth (work : ℕ) := RoleROM.bank (p.maskStart work+1) (3*p.rawEdges)
def Dated.slotStart (work : ℕ) := p.maskStart work+1+3*p.rawEdges+2*p.rawEdges

def Dated.ballotPage (rom work : ℕ) (j : Fin T) :=
  (p.ballot j).sheet p.sites (p.ballotROM rom j) (p.ballotStart work j) (p.fields j (p.siteROM rom) (p.siteStride rom) (p.roleStart work j.castSucc) (p.roleStart work j.succ))
def Dated.controlPage (rom work : ℕ) (j : Fin T) :=
  (p.control j).sheet p.sites (p.controlROM rom j) (p.controlBase work j) (p.controls j (p.siteStride rom) (p.roleStart work j.castSucc) (p.roleStart work j.succ) (p.ballotStart work j+1))

def triple : Expr := .op .add .row (.op .add .row .row)

def Dated.widthPage (rom work : ℕ) : Scatter :=
  let start := p.maskStart work
  let live : Expr := .lookup (RoleROM.bank (p.maskROM rom) p.rawEdges) .row
  let value : Expr := .branch .eq live (.lit 0) (.lit 0) (.lookup p.measured triple)
  ⟨start+1,3*p.rawEdges,start+1+3*p.rawEdges,p.rawEdges,.op .add (.lit (start+1)) triple,value⟩

def Dated.slotBase (work : ℕ) (side : Bool) := p.slotStart work+side.toNat*(1+3*p.rawEdges)+1
def Dated.slotBank (work : ℕ) (side : Bool) := RoleROM.bank (p.slotBase work side) p.rawEdges
def Dated.workEnd (work : ℕ) := p.slotStart work+2*(1+3*p.rawEdges)

def Dated.slotPage (work : ℕ) (side : Bool) : Scatter :=
  let B := p.slotBase work side
  ⟨B,p.rawEdges,B+p.rawEdges,p.rawEdges,.op .add (.lit B) .row,scale p.lanes (p.orderedSlot side)⟩

def Dated.last (T : ℕ) := (T+1)*3+(T+T)+2

def Dated.sheets (rom work : ℕ) : Fin (Dated.last T+1) → Scatter :=
  Fin.addCases
    (Fin.addCases (Fin.addCases (fun i=>let pair : Fin (T+1)×Fin 3 := finProdFinEquiv.symm i
                                        p.rolePage rom work pair.1 pair.2)
      (Fin.addCases (p.ballotPage rom work) (p.controlPage rom work)))
      (Fin.cases (p.widthPage rom work) (fun _=>p.slotPage work false)))
    (fun _=>p.slotPage work true)

theorem Dated.width_at (rom work : ℕ) :
    (p.widthPage rom work).base=(p.stageWidth work).base ∧
    (p.widthPage rom work).scratch+2*(p.widthPage rom work).rows=p.slotStart work := ⟨rfl,rfl⟩

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
