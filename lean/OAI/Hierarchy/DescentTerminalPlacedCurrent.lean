import OAI.Hierarchy.DescentTerminalBranchLeafReads
import OAI.Hierarchy.DescentTerminalPlacedHistogram
import OAI.Hierarchy.DescentTerminalChipBootWords
import OAI.Hierarchy.DescentTerminalFromChip

namespace OAI
/-! # Reached observations for the fixed five-scan terminal checker -/
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

def observationColumns {blocks : ℕ} (V : Home.Format) (cfg : Shape) (I : Input)
    (R : MaskAllocation.Channels blocks) (start header seedAt : ℕ) : Columns (I:=Unit) :=
  let regs := registers V cfg R start header
  let base := afterMeter V cfg R start
  let placed := layout cfg I base regs
  let plane := cfg.terminal.plane
  { seed := fun _ => regs.deadBits
    seedFlag := seedAt
    exteriorFlag := flagAt (j:=plane.headBits) (r:=plane.restBits) (t:=plane.bitLanes)
      (e:=plane.exteriors) (takeOff cfg I base)
    whole := ⟨wholeAddress cfg placed, 0⟩
    tail := ⟨tailAddress cfg placed, 0⟩
    keyBits := Nat.clog 2 cfg.terminal.rows }

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

/-- The selector observations and the private exponent are supplied at their genuine
earlier numeric addresses. Five cable columns and the attained branch print account
for all remaining fields of the host's original Current predicate. -/
theorem placed_current (early:Earlier cfg I ba (C).layout bitsW) (space:last V cfg I R start<2^bitsW)
    (seedPrior:seedAt<start) (count:0<(P).headerRows)
    (prior:∀i,(I.cable i).base+(I.cable i).size≤ start)
    (accepted:∀z:All,((out z) seedAt=0 ∧ (out z) fl=0)↔∃t,choice z=some t)
    (exponent:∀z:All,∀c,choice z=some c→(out z) (O).deadBits=((leaf c).debt cfg:Word bitsW))
    (bound:T→ℕ) (cover:∀c e,pairIndex (world c).graph (leaf c).home e<bound c)
    (length:∀c,(stream (world c).graph (leaf c).home (leaf c).native (leaf c).external (leaf c).nodes
      (leaf c).ops q (leaf c).hp (bound c)).length≤(P).headerRows)
    (widths:∀z c,choice z=some c→Reads (L).emit.plane.header
      (padded (n:=(P).headerRows) (stream (world c).graph (leaf c).home (leaf c).native (leaf c).external
        (leaf c).nodes (leaf c).ops q (leaf c).hp (bound c))) (before_ z))
    (prints:∀z c,choice z=some c→(leaf c).Printed cfg (arity:=arity) (groups:=groups) (stride:=stride)
      book L (C).layout (scratch z) banks cpu (poolBits z) outer (proposal z) B) :
    Current cols cpu banks old contents total_ count_ key_ out := by
  have m0:start≤(C).base:=Nat.le_add_right ..
  have upper:(O).deadBits<ba:=by change (C).base+_+cfg.sites+cfg.sites+2<(C).base+_+cfg.sites+cfg.sites+3;omega
  obtain ⟨s0,s1,s2,s3,s4⟩:=stages cfg I ba
  have lo:ba≤(cpu).first:=((rowArena cfg I ba).start_le 22).trans (s0.trans (s1.trans (s2.trans s3)))
  have origLow:orig+24*DescentExteriorShelf.span (P).headBits (P).restBits (P).bitLanes (P).exteriors≤(cpu).first:=by
    have step:orig+24*DescentExteriorShelf.span (P).headBits (P).restBits (P).bitLanes (P).exteriors≤
        DescentTerminalDataPlane.Arena.finish P orig:=by
      change orig+24*_≤orig+24*_+_+_+4*_+4*_;omega
    exact step.trans s3
  have flag:fl<(cpu).first:=by
    have n:=DescentExteriorShelf.row_room (P).headBits (P).restBits (P).bitLanes (P).exteriors
    change (P).exteriors*2^((P).headBits+(P).restBits)≤DescentExteriorShelf.span (P).headBits (P).restBits (P).bitLanes (P).exteriors at n
    have pos:0<DescentExteriorShelf.span (P).headBits (P).restBits (P).bitLanes (P).exteriors:=Nat.two_pow_pos (DescentExteriorShelf.exponent (P).headBits (P).restBits (P).bitLanes (P).exteriors)
    change orig+21*(DescentExteriorShelf.span (P).headBits (P).restBits (P).bitLanes (P).exteriors)+
      2*((P).exteriors*2^((P).headBits+(P).restBits))<_
    omega
  refine ⟨fun _=>upper.trans_le lo,⟨(eof_live cfg I ba O false count).2,
    (eof_live cfg I ba O true count).2⟩,⟨?_,flag⟩,accepted,fun z c seen _=>exponent z c seen,?_,?_,?_⟩
  · exact seedPrior.trans_le (m0.trans ((show (C).base≤ba by change (C).base≤(C).base+_+_+_+3;omega).trans lo))
  · intro z c seen
    let l:=leaf c
    have pos:0<d:=Nat.mul_pos l.qp l.hp
    have fit:=((suffix_room cfg I ba (C).layout O early space).issuer.plane.rawRoom)
    have room_:(P).rawRows<2^bitsW:=by
      have live:=DescentTerminalDataPlane.Arena.room ((P).rawRows+2+((P).publicRows+2))
      change _+DescentTerminalDataPlane.Arena.size ((P).rawRows+2+((P).publicRows+2))<2^bitsW at fit
      omega
    have x:total_ c/d≤(P).rawRows:=calc
      _ ≤ ((P).rawRows*d)/d := Nat.div_le_div_right l.volume
      _ = (P).rawRows := Nat.mul_div_cancel _ pos
    exact histogram V cfg I R start header short literal _ early space (world c).graph l.home l.native
      l.external l.nodes l.ops l.qp l.hp (bound c) (cover c) count (length c) prior (widths z c seen)
      (x.trans_lt room_) ((Nat.mod_lt _ pos).trans_le ((prints z c seen).wordFit.trans Nat.lt_two_pow_self.le))
  · intro z c seen
    exact (Leaf.printed_reads cfg (leaf c) book machine L (C).layout (scratch z) banks cpu (poolBits z) outer (proposal z) B (prints z c seen)).1
  · intro z c seen
    exact (Leaf.printed_reads cfg (leaf c) book machine L (C).layout (scratch z) banks cpu (poolBits z) outer (proposal z) B (prints z c seen)).2

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
