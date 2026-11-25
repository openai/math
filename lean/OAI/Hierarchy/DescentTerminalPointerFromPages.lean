import OAI.Hierarchy.DescentTerminalPointerIssue
import OAI.Hierarchy.DescentTerminalPointerArchive

namespace OAI
/-! # One attained memory from the previous books to the genuine numbered scalar operands -/
namespace Hierarchy.DescentTerminalPointerIssue
open Computability.BorderVNP.Crossing DescentSixParty DescentSharedCableNames DescentKernelHistory DescentTerminalPortChart
open DescentBundleHistory DescentTerminalBoundaryBasis DescentCompiler DescentColonies DescentLocalPrivateNames
open DescentOperandStateBanks DescentTerminalPointerDigits DescentTerminalChronologicalBooks
open ThreeFlat.Routing DescentTerminalVertexFields
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentSIMDLookup
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

section Reached
variable {F P J V Tag : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i p q N M K tags : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:AtomSchedule) (ready:A.StateBounds S i)
    (names:Stage.Host J V k↪ℕ) (v:W.graph.Site) (coords:Function.Injective (fun s=>(A.pos s,A.block s)))
    (port:Attached W.graph v↪ℕ) (hp:0<p) (scale psize:ℕ) (whole:A.z*G.b=scale*p)
    (common:∀z:Attached W.graph v,poolBatchCount (bits z.val) p=psize)
    (r:Recipe Tag (BlockRef p (boundaryWidth W.graph v))) (code:Tag→ Fin tags)
    (birth:r.Node↪ℕ) (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤M) (aliases:Slot r↪Fin K)
    (t:CellInputs A.degree A.cap N M)
local notation "rk" => rank A native S ready names v port
local notation "loc" => slot r birth nodes arity
local notation "chart" => (firstAlias r aliases).trans Fin.valEmbedding
local notation "G'" => W.graph
local notation "sparse" => Origin G' v r birth nodes arity aliases rk port t
local notation "sig" => Stage.signedPanel A native S ready names (Stage.home A v)


variable {hid groups blocks shops wb d0:ℕ} (config:Widths) (index:ℕ→ℕ→ℕ→ℕ)
    (pages:Gather.Pages blocks A.cap M) (before:Memory wb) (origin:ℕ) (machine:MaskedShelf blocks)
local notation "L" => columns A.cap N M
local notation "H" => blocks*shops
local notation "sz" => Nat.clog 2 (q+hid+1)
local notation "f7" => output A.cap N M A.degree groups d0 sz q scale psize config index
local notation "ps" => Gather.dropOff origin blocks shops L pages.address
local notation "warm" => ProtocolRAM.result ps before
local notation "src" => Gather.banks («L»:=L) origin H
local notation "base" => Gather.rom origin L H
local notation "start" => base+DescentTerminalPointerFrame.size L d0
local notation "after" => DescentTerminalPointerFrame.result base src H f7 warm
local notation "meas" => measured (q:=q) (t:=tags) («H»:=hid) (N:=N) (A:=M) (w:=p) (groups:=groups)
variable (b:Fin blocks) (h:Fin shops) (g:Fin groups)
local notation "cell" => pages.source (N:=N) (d:=d0) before b h
include coords whole common in
theorem primitive_from_pages
    (legal:∀j x,(pages.address (N:=N) j x).Fits origin shops wb)
    (off:2^d0<2^wb) (room:start+H<2^wb) (fits:sz*(N*M)*groups≤wb)
    (atBase:(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).base=start+b.val*shops)
    (keep:shops≤(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).size)
    (publicRoom:DescentTerminalGraphRows.arity G' p v≤q) (privateRoom:Fintype.card r.UsedWord≤hid)
    (read:SourceRead config cell g.val t)
    (prior:Origin G' v r birth nodes arity aliases rk port (reindexed t (index (cell mcol).val (cell fcol).val)))
    (chips:t.chips=sig) :
    ((ProtocolRAM.program wb ps).seq (DescentTerminalPointerFrame.program wb base src H f7)).Exec before after
      (ProtocolRAM.clock ps+((4+10*DescentTerminalPointerFrame.size L d0)+(4+H*(16+26*L)))) ∧
    CheapCode ((ProtocolRAM.program wb ps).seq (DescentTerminalPointerFrame.program wb base src H f7)) ∧
    (∀u (j:Fin (r.arity u)),
      venueField (cellAt (meas machine after h) (finProdFinEquiv (g,b)))
        (nodeArg (row r birth nodes u) (j.castLE (arity u)))=
      (((numbered G' hp v rk r.restricted code).operand u j).elim (fun a=>a.val+1) (fun a=>q+(ordinal chart a).val+1))) ∧
    (∀a,a<origin ∨ start+H≤a→ after a=before a) ∧
    ProtocolRAM.clock ps≤4+(L*blocks)*(4+shops*18) := by
  have all:=pages.execute before origin shops f7 legal off room
  have beforeROM : origin+(L*blocks)*shops≤base:=by rw [Nat.mul_assoc];exact Nat.le_add_right _ _
  have inputs:=pages.fetched (d:=d0) before origin shops legal (by omega) b h
  have typed:=primitive_rows (q:=q) (hid:=hid) A native S ready names v coords port hp scale psize whole common r code birth nodes arity
    aliases t config index base src warm machine (Gather.banks_fit origin H d0 off room) b h g fits atBase keep
      publicRoom privateRoom (by rw [inputs];exact read) (by rw [inputs];exact prior) chips
  exact ⟨all.1,all.2.1,typed.2.2.1,all.2.2.2.1,all.2.2.2.2⟩

end Reached
end
end Hierarchy.DescentTerminalPointerIssue

end OAI
