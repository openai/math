import OAI.Hierarchy.DescentTerminalSlottedPrefix
import OAI.Hierarchy.DescentTerminalMaskedRAM
import OAI.Hierarchy.DescentTerminalPositionIssue

namespace OAI
/-! # Terminal CPU from the actual slotted site order and sparse reached archives -/
namespace Hierarchy.DescentTerminalCompiledPrefix
open DescentTerminalVertexFields Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {w blocks : ℕ} (S : Shape) (L : Layout) (F : MaskedShelf blocks)
attribute [local irreducible] Procedure.Exec CheapCode
local notation "before" => slotted S L
local notation "maskProgram" => scan w L.directory.texture.base (S.sites+1) (guardedMask F S.sites)
local notation "issue" => scan w L.emit.leaf.event.base S.terminal.pool (DescentTerminalSiteShelves.gather L.directory)
local notation "ending" => DescentTerminalEmitter.program (w:=w) S.terminal L.emit

def afterMask (m : Memory w) := maskedMem F L.directory S.sites (before m)
def maskEvents (m : Memory w) := DescentTerminalEmitter.issued S.terminal L.emit L.directory (afterMask S L F m)
def maskResult (m : Memory w) := DescentTerminalEmitter.result S.terminal L.emit (maskEvents S L F m)
def maskMachine := ((slottedPrefix (w:=w) S L).seq maskProgram).seq ((issue).seq ending)
def maskClocks := (slottedClocks S L+(4+(S.sites+1)*(26+234*blocks)))+
  ((4+S.terminal.pool*(2*(DescentTerminalSiteShelves.gather L.directory).work+4))+DescentTerminalEmitter.time S.terminal L.emit)

theorem mask_exec (m : Memory w) (room : Room S L w) (positive : 0<w)
    (allocation : L.row.mark.Fixed S.sites (DescentTerminalRowPlan.header L.row S.sites (counted S L m)))
    (slotRoom : slotBase S L+S.packets<2^w) (fields : (guardedMask F S.sites).Fits w L.directory.texture.base)
    (pages : L.directory.texture.base+(S.sites+1)<2^w) (fixed : DescentTerminalEmitter.Static S.terminal L.emit (maskEvents S L F m)) :
    (maskMachine (w:=w) S L F).Exec m (maskResult S L F m) (maskClocks (blocks:=blocks) S L) ∧ CheapCode (maskMachine (w:=w) S L F) := by
  have «prefix»:=slotted_run S L m room positive allocation slotRoom
  have scalar:=mask_run F L.directory (before m) fields pages
  have result:=DescentTerminalEmitter.issue_run S.terminal L.emit L.directory (afterMask S L F m) positive room.emit room.loadPages room.pageClock fixed
  exact exec_cheap_seq (exec_cheap_seq «prefix» scalar) result

end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
