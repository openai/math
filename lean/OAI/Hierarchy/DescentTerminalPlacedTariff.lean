import OAI.Hierarchy.DescentTerminalPlacedCapacity
import OAI.Hierarchy.DescentTerminalEmitterNames
import OAI.Hierarchy.DescentTerminalMaskInvoice

namespace OAI
/-! # The complete fixed-width terminal invoice including every static instruction -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn DescentTerminalVertexFields DescentTerminalRowArena
open DescentCompiler.TerminalScale
noncomputable section
variable {blocks v B bw:ℕ} (V:Home.Format) (S:Shape) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)
local notation "C" => meter V R start
local notation "O" => registers V S R start header
local notation "ba" => afterMeter V S R start
local notation "L" => layout S I ba O
local notation "arena_" => rowArena S I ba
local notation "cpu" => clock V S I R start header short literal (bw:=bw)
local notation "ticks" => time V S I R start header
local notation "cap_" => cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
 (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "sz" => channelSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
 (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "cells" => MaskAllocation.marks sz+cap_
local notation "static" => DescentTerminalEmitter.Compact.wordsBought I.sources
local notation "oldLabels" => privateMaskedNames cells cap_ blocks V.piece
local notation "oldTicks" => privateMaskedClock cells cap_ S.sites blocks V.piece

theorem instruction_bound :
    names cpu≤oldLabels+15*(static+1)+6972+468*blocks := by
  have low:=PrivateCounter.hardware (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
    (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=S.sites) (bw:=bw) C O
  have init:=(arena_).prime_text bw
  change names ((arena_).prime bw)=110 at init
  unfold clock tailCode
  simp only [names_seq,DescentTerminalEmitter.Compact.labels,MaskAllocation.program,names_mount,init,
    Suffix.names,DescentTerminalEmitter.names_exact]
  unfold privateMaskedNames privateHomeNames MaskAllocation.marks
  omega

/-- Includes the five candidate checks and printed key scan subsequently issued by the
fixed host, alongside its seven opcode columns. All terms are physical word counts. -/
theorem paid_program (paid:ℕ) (rows:RowCap S L paid) (src:DescentTerminalChipRuntime.Banks) :
    ticks+DescentTerminalChipRuntime.clocks S.terminal.rows S.terminal.pool+
        7*(names cpu+names (DescentTerminalChipRuntime.program (chip S I ba) src bw S.terminal.rows S.terminal.pool))≤
      oldTicks+7*oldLabels+115*(static+1)+
        24*(4+(S.sites+1)*(26+234*blocks))+131072*(S.sites+S.packets+paid+1) := by
  have text:=instruction_bound V S I R start header short literal (bw:=bw)
  have charged:=rows.price blocks
  have y:=rows.routes;have z:=rows.packed
  have side:468*blocks≤2*((S.sites+1)*(26+234*blocks)):=by
    have step : 26+234*blocks ≤ (S.sites+1)*(26+234*blocks) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos S.sites)
    omega
  rw [DescentTerminalChipRuntime.program_names]
  unfold time DescentTerminalChipRuntime.clocks privateMaskedClock
  omega

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
