import OAI.Hierarchy.DescentTerminalPlacedCurrent
import OAI.Hierarchy.DescentTerminalObservedFlight

namespace OAI
/-! # Pin, execution and genuine chip observations of the physically placed terminal flight -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalChipPins DescentTerminalChipRuntime DescentTerminalEmitter.Branch
open DescentTerminalBinReaddress DescentTerminalPorts DescentTerminalDenseWindow DescentTerminalScalarTransposes
open DescentSixParty DescentCompiler DescentBundleHistory DescentEpochTagKeys
open DescentKernelHistory hiding Word
open DescentTerminalDenseHeaderRAM DescentTerminalHeaderGroups DescentTerminalCableOrder Computability.BorderVNP.Crossing
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalVertexFields DescentExteriorShelf DescentExterior
open scoped BigOperators
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Port Tag T Opaque : Type} [Field F] [Fintype Port] {ew:Port→ℕ}
variable {D k age zStage degree wire hist K W q piece bitsW H nodesN addrN verts initial arity groups stride : ℕ}
variable {G:PoweredGadget F} {ε price:ℝ} {σ:AtomSchedule}
variable {v B:ℕ} (V:Home.Format) (cfg:Shape) (I:Input) (R:MaskAllocation.Channels (2^k))
variable (start header seedAt:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)
local notation "p" => W*piece
local notation "d" => q*p
local notation "cap" => DescentBundleTagKeys.capacity initial arity groups p stride
local notation "C" => meter V R start
local notation "O" => registers V cfg R start header
local notation "ba" => afterMeter V cfg R start
local notation "L" => layout cfg I ba O
local notation "P" => cfg.terminal.plane
local notation "cpu" => chip cfg I ba
local notation "orig" => takeOff cfg I ba
local notation "fl" => flagAt (j:=(P).headBits) (r:=(P).restBits) (t:=(P).bitLanes) (e:=(P).exteriors) orig
local notation "RBits" => RowBit (P).rawRows d→Bool
local notation "All" => DescentTerminalRAM.Choice (Opaque⊕DescentTerminalChipPins.Inputs K W q piece) (P).rawRows d→Bool

variable (world:T→MarkedWorld F D Port ew)
    (reached:∀c,DescentSixParty.Reached (world c) G price ε σ k age zStage degree wire hist)
    (leaf:∀c,Leaf cfg (world c) (reached c) Tag W q piece H nodesN addrN verts)
    (book:Codec Tag initial) (machine:sliceWidth W q piece≤bitsW)
variable (outer:Computability.BorderVNP.Crossing.Ports ew)
    (before_:(DescentTerminalRAM.Choice (Opaque⊕DescentTerminalChipPins.Inputs K W q piece) cfg.terminal.plane.rawRows
      (q*(W*piece))→Bool)→Memory bitsW)
    (old:(RowBit cfg.terminal.plane.rawRows (q*(W*piece))→Bool)→(Opaque→Bool)→Option T)
variable (front empty:ℕ)
local notation "codes" => DescentTerminalScalarHeader.range q cap H nodesN addrN p verts
local notation "banks" => DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=q) («p»:=piece) codes (L).emit front empty
local notation "cols" => observationColumns V cfg I R start header seedAt
local notation "out" => fun z:All=>output V cfg I R start header short literal (before_ z)
local notation "scratch" => fun z:All=>(rowArena cfg I ba).mount (input V cfg I R start header short literal (before_ z))
local notation "total_" => fun c:T=>∑e,(world c).graph.width e
local notation "count_" => fun (c:T) (_:Unit)=>(leaf c).debt cfg
local notation "contents" => fun (c:T) (x:RBits)=>(leaf c).contents cfg (K₀:=K) x outer
local notation "key_" => fun (c:T) (x:RBits)=>(leaf c).keys cfg (arity:=arity) (groups:=groups) (stride:=stride) book machine x outer
local notation "choice" => fun z:All=>old (poolBits z) (erased z)

variable {Ext:Type} (external:Ext→Bool) {S0 ticks:ℕ} (Q:Procedure bitsW)
variable (pins : Fin S0 × Fin (bitsW+1) →
    (Ext ⊕ DescentTerminalRAM.Choice (Opaque ⊕ DescentTerminalChipPins.Inputs K W q piece)
      cfg.terminal.plane.rawRows (q*(W*piece))) ⊕ Bool)
    (headerWords : (DescentTerminalRAM.Choice (Opaque ⊕ DescentTerminalChipPins.Inputs K W q piece)
      cfg.terminal.plane.rawRows (q*(W*piece)) → Bool) → ℕ → Word bitsW)

theorem placed_flight (early:Earlier cfg I ba (C).layout bitsW) (space:last V cfg I R start<2^bitsW)
    (seedPrior:seedAt<start) (count:0<(P).headerRows)
    (prior:∀i,(I.cable i).base+(I.cable i).size≤ start)
    (run:∀z:All,Flight Q S0 ticks pins external z (headerWords z) (out z) seedAt fl (O).deadBits (choice z)
      (fun t=>(leaf t).debt cfg))
    (bound:T→ℕ) (cover:∀c e,pairIndex (world c).graph (leaf c).home e<bound c)
    (length:∀c,(stream (world c).graph (leaf c).home (leaf c).native (leaf c).external (leaf c).nodes
      (leaf c).ops q (leaf c).hp (bound c)).length≤(P).headerRows)
    (widths:∀z c,choice z=some c→Reads (L).emit.plane.header
      (padded (n:=(P).headerRows) (stream (world c).graph (leaf c).home (leaf c).native (leaf c).external
        (leaf c).nodes (leaf c).ops q (leaf c).hp (bound c))) (before_ z))
    (prints:∀z c,choice z=some c→(leaf c).Printed cfg (arity:=arity) (groups:=groups) (stride:=stride)
      book L (C).layout (scratch z) banks cpu (poolBits z) outer (proposal z) B) :
    (∀z:All,∀i,Sum.elim (Sum.elim external z) id (pins i)=
      ThreeFlat.Diagonal.TraceWords.bits
        (ThreeFlat.Diagonal.TraceBanks.wide (headerWords z i.1.val)) i.2) ∧
    (∀z:All,Q.Exec (Computability.VPVNP.RAMMemory.initialMemory S0 (headerWords z)) (out z) ticks) ∧
    CheapCode Q ∧ Current cols cpu banks old contents total_ count_ key_ out := by
  refine ⟨fun z=>(run z).pins_at,fun z=>(run z).executed,(run fun _=>false).cheap,?_⟩
  exact placed_current (V:=V) (cfg:=cfg) (I:=I) (R:=R) (start:=start) (header:=header) (seedAt:=seedAt)
    (short:=short) (literal:=literal) (world:=world) (reached:=reached) (leaf:=leaf) (book:=book)
    (machine:=machine) (outer:=outer) (before_:=before_) (old:=old) (front:=front) (empty:=empty)
    early space seedPrior count prior (fun z=>(run z).admitted) (fun z c=>(run z).seed c)
    bound cover length widths prints

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
