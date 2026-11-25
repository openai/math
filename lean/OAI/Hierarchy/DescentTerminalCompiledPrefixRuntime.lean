import OAI.Hierarchy.DescentTerminalSuffixData
import OAI.Hierarchy.DescentTerminalPacketSort
import OAI.Hierarchy.DescentTerminalRowOwner
import OAI.Hierarchy.DescentTerminalSiteOffsets
import OAI.Hierarchy.DescentTerminalPositionGather
import OAI.Hierarchy.DescentTerminalEmittedAdmission
import OAI.Hierarchy.DescentTerminalEmittedCutoff
import OAI.Hierarchy.DescentTerminalEmitterPrice
import OAI.Hierarchy.DescentPackedExponentCheap

namespace OAI
/-! # One fixed native program from short archived terminal geometry to the actual bit-plane checks -/
namespace Hierarchy.DescentTerminalCompiledPrefix
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {w : ℕ}

variable (S : Shape) (L : Layout)
set_option quotPrecheck false
local notation "orderProgram" => DescentTerminalExteriorPackets.sortedProgram L.homes L.order S.sites S.packets w
local notation "orderWork" => (4+S.packets*(2*(DescentTerminalExteriorPackets.guard L.homes S.sites).work+4))+ProtocolRAMEndpointSort.cost S.packets S.sites
local notation "N" => S.terminal.rows
local notation "counter" => DescentPackedTerminalExponent.program L.count L.exponent w S.nodes S.batch S.piece
local notation "rowProgram" => DescentTerminalRowPlan.program (w:=w) L.row S.sites N
local notation "record" => DescentTerminalSiteShelves.gather L.directory
local notation "pageProgram" => scan w L.emit.leaf.event.base S.terminal.pool record
local notation "machine" => DescentTerminalEmitter.program (w:=w) S.terminal L.emit

def counted (m : Memory w) := DescentPackedTerminalExponent.image L.count L.exponent S.nodes S.batch S.piece m
def allocated (m : Memory w) := DescentTerminalRowPlan.result L.row S.sites N (counted S L m)
def rowed (m : Memory w) := DescentTerminalSiteOffsets.result L.offset S.sites (allocated S L m)
def ordered (m : Memory w) := DescentTerminalExteriorPackets.sorted L.homes L.order S.sites S.packets S.sites_pos (rowed S L m)
def planned (m : Memory w) := image L.emit.leaf.event.base S.terminal.pool record (ordered S L m)
def result (m : Memory w) := DescentTerminalEmitter.result S.terminal L.emit (planned S L m)
def program := (((((counter).seq rowProgram).seq (DescentTerminalSiteOffsets.program L.offset w S.sites)).seq orderProgram).seq pageProgram).seq machine
def clocks := (DescentPackedPrivateSum.Layout.billed 1 S.nodes S.batch+DescentPrivateExponentRAM.steps L.exponent S.piece)+
  DescentTerminalRowPlan.time L.row S.sites N+DescentTerminalSiteOffsets.time L.offset S.sites+orderWork+(4+S.terminal.pool*(2*(record).work+4))+DescentTerminalEmitter.time S.terminal L.emit

structure Room (w : ℕ) : Prop where
  packed : L.count.Room w 1 S.nodes S.batch
  scalar : L.exponent.Room w
  plan : DescentTerminalRowPlan.Room L.row S.sites N w
  offset : DescentTerminalSiteOffsets.Room L.offset w S.sites
  ordering : DescentTerminalExteriorPackets.SortRoom L.homes L.order w S.packets S.sites
  loadPages : (record).Fits w L.emit.leaf.event.base
  pageClock : L.emit.leaf.event.base+S.terminal.pool<2^w
  emit : DescentTerminalEmitter.Room S.terminal L.emit w

/-- The only prescribed bytes on an arbitrary rejected selector path are the
alternating 0/1 address-or-value lanes driving three bounded scatter loops. -/
structure Lanes (m : Memory w) : Prop where
  allocation : L.row.mark.Fixed S.sites (DescentTerminalRowPlan.header L.row S.sites (counted S L m))
  terminal : DescentTerminalEmitter.Static S.terminal L.emit (planned S L m)

theorem run (m : Memory w) (room : Room S L w) (pos : 0<w) (rom : Lanes S L m) :
    (program (w:=w) S L).Exec m (result S L m) (clocks S L) ∧ CheapCode (program (w:=w) S L) := by
  have a : (counter).Exec m (counted S L m)
      (DescentPackedPrivateSum.Layout.billed 1 S.nodes S.batch+DescentPrivateExponentRAM.steps L.exponent S.piece) ∧
      CheapCode (counter) :=
    ⟨@DescentPackedTerminalExponent.run w L.count L.exponent S.nodes S.batch S.piece m room.packed room.scalar,
      @DescentPackedTerminalExponent.cheap L.count L.exponent w S.nodes S.batch S.piece⟩
  have b:=DescentTerminalRowPlan.run L.row S.sites N (counted S L m) room.plan pos rom.allocation
  have r:=DescentTerminalSiteOffsets.run L.offset S.sites (allocated S L m) room.offset
  have o:=DescentTerminalExteriorPackets.sort_run L.homes L.order S.sites S.packets (rowed S L m) S.sites_pos room.ordering
  have g : (pageProgram).Exec (ordered S L m) (planned S L m) (4+S.terminal.pool*(2*(record).work+4)) ∧
      CheapCode (pageProgram) :=
    ⟨@scan_exec w L.emit.leaf.event.base S.terminal.pool record (ordered S L m) room.loadPages room.pageClock,
      @scan_cheap w L.emit.leaf.event.base S.terminal.pool record⟩
  have c:=DescentTerminalEmitter.run S.terminal L.emit (planned S L m) pos room.emit rom.terminal
  unfold program clocks result
  exact exec_cheap_seq (exec_cheap_seq (exec_cheap_seq (exec_cheap_seq (exec_cheap_seq a b) r) o) g) c

theorem native_tariff :
    clocks S L≤DescentPackedPrivateSum.Layout.billed 1 S.nodes S.batch+DescentPrivateExponentRAM.steps L.exponent S.piece+
      1104*(S.sites+S.terminal.rows+S.packets+1)+4608*DescentTerminalEmitter.volume S.terminal L.emit := by
  have sortWork:=DescentTerminalExteriorPackets.ticks L.homes S.sites S.packets
  have a:=DescentTerminalRowPlan.tariff L.row S.sites S.terminal.rows
  have b:=DescentTerminalEmitter.clocks S.terminal L.emit
  have per:2*(record).work+4≤512:=by change 2*137+4≤512; decide
  have g:=Nat.mul_le_mul_left S.terminal.pool per
  have volume:S.terminal.pool+1≤DescentTerminalEmitter.volume S.terminal L.emit:=by unfold DescentTerminalEmitter.volume;omega
  unfold clocks
  rw [DescentTerminalSiteOffsets.time_eq]
  omega


end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
