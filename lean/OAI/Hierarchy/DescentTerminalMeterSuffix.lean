import OAI.Hierarchy.DescentTerminalSuffixFits
import OAI.Hierarchy.DescentTerminalSuffixData
import OAI.Hierarchy.DescentTerminalMaskedAdmission

namespace OAI
/-! # Running the terminal allocation and both physical flights after the reached private meter -/

namespace Hierarchy.DescentTerminalCompiledPrefix
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalVertexFields
noncomputable section

namespace Suffix
variable {w blocks : ℕ} (S : Shape) (L : Layout) (F : MaskedShelf blocks)
local notation "rows_" => S.terminal.rows
local notation "plan" => DescentTerminalRowPlan.program (w:=w) L.row S.sites rows_
local notation "offsets" => DescentTerminalSiteOffsets.program L.offset w S.sites
local notation "publish_" => DescentTerminalPacketSlotRAM.program L.homes L.order w S.packets S.sites
local notation "mask" => scan w L.directory.texture.base (S.sites+1) (guardedMask F S.sites)
local notation "emitLeaf" => scan w L.emit.leaf.event.base S.terminal.pool (DescentTerminalSiteShelves.gather L.directory)
local notation "finalStage" => DescentTerminalEmitter.program (w:=w) S.terminal L.emit

def program := (((((plan).seq offsets).seq publish_).seq mask).seq ((emitLeaf).seq finalStage))

def slotsTime :=
  (DescentTerminalRowPlan.time L.row S.sites rows_+DescentTerminalSiteOffsets.time L.offset S.sites)+
  ((4+S.packets*(2*(DescentTerminalExteriorPackets.guard L.homes S.sites).work+4))+
    ProtocolRAMEndpointSort.cost S.packets S.sites+(4+S.packets*80))
def time (blocks : ℕ) := (slotsTime S L+(4+(S.sites+1)*(26+234*blocks)))+
  ((4+S.terminal.pool*(2*(DescentTerminalSiteShelves.gather L.directory).work+4))+
    DescentTerminalEmitter.time S.terminal L.emit)

/-- There is no second pass over private operands. The argument is the exact
output of the earlier home counter on this candidate header. -/
theorem run (m : Memory w) (room : Fits S L F w) (pos : 0<w)
    (fixedPlan : L.row.mark.Fixed S.sites (DescentTerminalRowPlan.header L.row S.sites m))
    (fixedEmit : DescentTerminalEmitter.Static S.terminal L.emit (events S L F m)) :
    (program (w:=w) S L F).Exec m (output S L F m) (time S L blocks) ∧ CheapCode (program (w:=w) S L F) := by
  have plan_:=DescentTerminalRowPlan.run L.row S.sites rows_ m room.allocator pos fixedPlan
  have offsets_:=DescentTerminalSiteOffsets.run L.offset S.sites (DescentTerminalRowPlan.result L.row S.sites rows_ m) room.offsets
  have sort:=DescentTerminalPacketSlotRAM.run L.homes L.order (positioned S L m) S.sites_pos room.sort room.endSlots
  have mark:=mask_run F L.directory (sockets S L m) room.pageROM room.endPages
  have issue:=DescentTerminalEmitter.issue_run S.terminal L.emit L.directory (pages S L F m) pos room.issuer
    room.leafROM room.endLeaves fixedEmit
  exact exec_cheap_seq (exec_cheap_seq (exec_cheap_seq (exec_cheap_seq plan_ offsets_) sort) mark) issue

theorem agrees (m : Memory w) : output S L F (counted S L m)=maskResult S L F m := rfl

theorem early (m : Memory w) (room : Fits S L F w) {a : ℕ} (keep : Frozen L a)
    (slot : a<slotBase S L) (page : a<L.directory.texture.base) :
    events S L F m a=m a := by
  rw [events,DescentTerminalEmitter.issued,DescentTerminalChipRuntime.image_low _ _ _ _ keep.pages,
    pages,maskedMem,DescentTerminalChipRuntime.image_low _ _ _ _ page,sockets,
    DescentTerminalPacketSlotRAM.retained L.order S.packets S.sites _ a (.inl slot),
    DescentTerminalExteriorPackets.sort_before _ _ _ _ _ _ room.sort keep.sort,
    positioned,DescentTerminalSiteOffsets.early _ _ _ keep.offsets,
    DescentTerminalRowPlan.before_publishing _ _ room.allocator keep.memories keep.books]

theorem saved (m : Memory w) (room : Fits S L F w) {a : ℕ}
    (keep : Frozen L a) (slot : a<slotBase S L) (page : a<L.directory.texture.base)
    (lo : DescentTerminalEmitter.BeforeKey S.terminal L.emit a)
    (hi : DescentTerminalEmitter.AfterFlights S.terminal L.emit a) :
    output S L F m a=m a := by
  rw [output,DescentTerminalEmitter.printed_before _ _ _ room.issuer lo hi,early S L F m room keep slot page]

end Suffix
end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
