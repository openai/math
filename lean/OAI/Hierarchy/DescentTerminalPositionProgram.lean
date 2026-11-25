import OAI.Hierarchy.DescentTerminalCompiledPrefix
import OAI.Hierarchy.DescentTerminalPositionIssue
import OAI.Hierarchy.DescentTerminalReachedPanels

namespace OAI
/-! # The terminal program from eight actual short local scalar-field columns -/
namespace Hierarchy.DescentTerminalCompiledPrefix
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalVertexFields
noncomputable section
variable {w : ℕ} (S : Shape) (L : Layout) (F : Shelf)
local notation "orderProgram" => DescentTerminalExteriorPackets.sortedProgram L.homes L.order S.sites S.packets w
local notation "N" => S.terminal.rows
local notation "counter" => DescentPackedTerminalExponent.program L.count L.exponent w S.nodes S.batch S.piece
local notation "plan" => DescentTerminalRowPlan.program (w:=w) L.row S.sites N
local notation "record" => DescentTerminalSiteShelves.gather L.directory
local notation "loadPages" => scan w L.emit.leaf.event.base S.terminal.pool record
local notation "machine" => DescentTerminalEmitter.program (w:=w) S.terminal L.emit


local notation "publish" => scan w L.directory.texture.base (S.sites+1) (pageRow S.sites F)

def issuedPanels (m : Memory w) := rendered S.sites F L.directory (ordered S L m)
def paged (m : Memory w) := DescentTerminalEmitter.issued S.terminal L.emit L.directory (issuedPanels S L F m)
def panelResult (m : Memory w) := DescentTerminalEmitter.result S.terminal L.emit (paged S L F m)
def panelProgram := (((((counter).seq plan).seq (DescentTerminalSiteOffsets.program L.offset w S.sites)).seq orderProgram).seq publish).seq ((loadPages).seq machine)

theorem panel_run (m : Memory w) (room : Room S L w) (pos : 0<w)
    (sourceFits : (pageRow S.sites F).Fits w L.directory.texture.base) (pageClock : L.directory.texture.base+(S.sites+1)<2^w)
    (allocation : L.row.mark.Fixed S.sites (DescentTerminalRowPlan.header L.row S.sites (counted S L m)))
    (hardware : DescentTerminalEmitter.Static S.terminal L.emit (paged S L F m)) :
    (panelProgram (w:=w) S L F).Exec m (panelResult S L F m) (clocks S L+4+234*(S.sites+1)) ∧ CheapCode (panelProgram (w:=w) S L F) := by
  have a : (counter).Exec m (counted S L m)
      (DescentPackedPrivateSum.Layout.billed 1 S.nodes S.batch+DescentPrivateExponentRAM.steps L.exponent S.piece) ∧
      CheapCode (counter) :=
    ⟨@DescentPackedTerminalExponent.run w L.count L.exponent S.nodes S.batch S.piece m room.packed room.scalar,
      @DescentPackedTerminalExponent.cheap L.count L.exponent w S.nodes S.batch S.piece⟩
  have b:=DescentTerminalRowPlan.run L.row S.sites N (counted S L m) room.plan pos allocation
  have r:=DescentTerminalSiteOffsets.run L.offset S.sites (allocated S L m) room.offset
  have o:=DescentTerminalExteriorPackets.sort_run L.homes L.order S.sites S.packets (rowed S L m) S.sites_pos room.ordering
  have f:=render F L.directory (ordered S L m) sourceFits pageClock
  have g:=DescentTerminalEmitter.issue_run S.terminal L.emit L.directory (issuedPanels S L F m) pos room.emit
    room.loadPages room.pageClock hardware
  have issued := exec_cheap_seq (exec_cheap_seq (exec_cheap_seq (exec_cheap_seq (exec_cheap_seq a b) r) o) f) g
  simpa only [panelProgram,panelResult,paged,clocks,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using issued

end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
