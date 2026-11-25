import OAI.Hierarchy.DescentTerminalPlacedProgram
import OAI.Hierarchy.DescentTerminalMaskReady

namespace OAI
/-! # Complete fixed-clock terminal processor on every proposed input image -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalSiteShelves DescentTerminalRowArena
noncomputable section
set_option quotPrecheck false

variable {blocks v B bw:ℕ} (V:Home.Format) (S:Shape) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)

local notation "C" => meter V R start
local notation "O" => registers V S R start header
local notation "base_" => afterMeter V S R start
local notation "L" => layout S I base_ O
local notation "Csize" => cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
    (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "num" => channelSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
    (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "mx" => MaskAllocation.program (groups:=V.groups) (blocks:=blocks) short bw start
local notation "ix" => MaskAllocation.image (groups:=V.groups) (blocks:=blocks) short start
local notation "color" => DescentTerminalEmitter.Compact.install (pageEnd S I base_) I.sources literal bw
local notation "shelves" => DescentTerminalEmitter.Compact.loaded (pageEnd S I base_) I.sources literal
local notation "priv" => PrivateCounter.machine (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
    (N:=V.nodes) (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=S.sites) (bw:=bw) C O
local notation "count_" => Home.measured V S C O
local notation "literalCost" => (4+10*DescentTerminalEmitter.Compact.wordsBought I.sources)+
  (4+10*(MaskAllocation.marks num+Csize))
local notation "privateTime" => DescentCompiler.TerminalScale.privateHomeClock Csize S.sites blocks V.piece

/-- The small state following private correction and original static table installation. -/
def input (m:Memory bw) := count_ (ix (shelves m))
def clock : Procedure bw := (((color).seq mx).seq priv).seq (tailCode S I base_ (C).layout O)
def output (m:Memory bw) := tailImage S I base_ (C).layout O (input V S I R start header short literal m)
def time := (literalCost+privateTime)+((8+104*S.sites)+Suffix.time S L blocks)

theorem run (m:Memory bw) (low:∀f,(R.bank f).base+(R.bank f).size≤ start) (hdr:header<start)
    (early:Earlier S I base_ (C).layout bw) (space:last V S I R start<2^bw) (positive:0<bw) :
    (clock V S I R start header short literal (bw:=bw)).Exec m (output V S I R start header short literal m)
        (time V S I R start header) ∧ CheapCode (clock V S I R start header short literal (bw:=bw)) := by
  have enough:=fits V S I R start header low hdr early space
  obtain ⟨p0,p1,p2,p3,p4⟩:=stages S I base_
  have end_:endAddress S I base_<2^bw:=space
  have finalRoom:=p2.trans_lt (p3.trans_lt (p4.trans_lt end_))
  have misc:=DescentTerminalEmitter.Compact.load (pageEnd S I base_) I.sources literal m finalRoom
  have miscRun : (color).Exec m (shelves m) (4+10*DescentTerminalEmitter.Compact.wordsBought I.sources)
      ∧ CheapCode (color) := ⟨@misc.1, @misc.2.1⟩
  have maskRoom : start+(MaskAllocation.marks num+Csize)<2^bw :=
    (Nat.le_add_right (start+(MaskAllocation.marks num+Csize)) Csize).trans_lt enough.home.space
  have initial:=MaskAllocation.install_at R start short (shelves m) (bw:=bw) (groups:=V.groups)
    maskRoom
  have maskRun : (mx).Exec (shelves m) (ix (shelves m)) (4+10*(MaskAllocation.marks num+Csize))
      ∧ CheapCode (mx) := ⟨@initial.1, @initial.2.2.2⟩
  have meter_:=PrivateCounter.any_raw (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
    (N:=V.nodes) (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=S.sites)
    C O (ix (shelves m)) enough.home enough.endHome enough.scalar
  have rest:=tail_run S I base_ (C).layout O (input V S I R start header short literal m) early end_ positive
  exact exec_cheap_seq (exec_cheap_seq (exec_cheap_seq miscRun maskRun) meter_) rest

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
