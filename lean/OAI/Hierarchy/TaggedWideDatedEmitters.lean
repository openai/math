import OAI.Hierarchy.TaggedWideDatedOperands
import OAI.Hierarchy.TaggedWideRoleScatter
import OAI.ThreeFlat.RAM.ProcedureBank

namespace OAI
/-! # The three native role emitters and their external memory operands -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets
open ProtocolRAM RoleProgram
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing

def role : Fin 3→RoleField := ![.width,.ordinal,.opposite]
variable (n : ℕ) (chart : Chart) (sock : Bool→Socket) (siteTable : Bank) (size number : Expr)
local notation "self" => DatedRows.split n sock false
local notation "peer" => DatedRows.split n sock true
local notation "sz" => DatedRows.each n size size
local notation "idWord" => DatedRows.each n number number

def word (f : Fin 3) : Expr := (role f).expr sz idWord (socketSite chart peer)
def dest (start L : ℕ) (f : Fin 3) : Expr :=
  RoleWidths.destination (sheet start L n f) (sink start L n f) (word n chart sock size number f)
    (RoleWidths.offset siteTable (socketSite chart self) (socketCode chart self))

def leaf (native start L : ℕ) (f : Fin 3) : Procedure native :=
  ProtocolRAMTurnReplay.program native (sheet start L n f) L (sheet start L n f+L) (n+n)
    (dest n chart sock siteTable size number start L f) (word n chart sock size number f)

def leafWork (start L : ℕ) (f : Fin 3) :=
  ProtocolRAMTurnReplay.work L (n+n) (dest n chart sock siteTable size number start L f) (word n chart sock size number f)

def program (native start L : ℕ) : Procedure native :=
  ProcedureBank.program 2 (leaf n chart sock siteTable size number native start L)

def work (start L : ℕ) :=
  let cost:=leafWork n chart sock siteTable size number start L
  cost 0+(cost 1+cost 2)

/-- All reads in a frame come from the already committed prefix of memory. -/
structure Fits (native start : ℕ) : Prop where
  size : (sz).Fits native start
  number : (idWord).Fits native start
  selfSite : (socketSite chart self).Fits native start
  selfCode : (socketCode chart self).Fits native start
  peerSite : (socketSite chart peer).Fits native start
  peerCode : (socketCode chart peer).Fits native start
  table : siteTable.Fits native start

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets

end
end OAI
