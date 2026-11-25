import OAI.Computability.BorderVNP.DiagonalSourceLookupWords
import OAI.Computability.BorderVNP.DiagonalSourceOwnedLookup

/-! # Lookup of the signed packet at the ownership return of the reconstructed source -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open PackedHistoryCircuit
open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Scatter Scatter.Assignment SignedPrep TeamRows Tally
open DiagonalTallyPacketEmit CellMacro.Generator JointHeader ProcessorSlots SignedTaskArena FiniteEvaluator
set_option maxHeartbeats 1500000
set_option maxRecDepth 7500

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} (sa : SignedTaskArena.Layout) {decl : LengthDeclaration sa.cube.n sa.cube.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w}
    {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks →
      Selector sa.cube.n sa.cube.K sa.cube.h) → Fin sa.cube.header.d → Fin (R+1)}
    (S : SourceReports sa.cube owners) (F : PreparationFrame G L sa.cube decl header pin pub mac reg mem)
    (B : F.Builders fixed sa.id owners) (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared sa.cube owners decl // S.pins v.val}) (reports : S.actual q.val.val)

local notation3 (prettyPrint := false) "full" => (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩
local notation3 (prettyPrint := false) "raw" => declaredWords sa.cube owners decl q.val
local notation3 (prettyPrint := false) "z" => F.replay fixed raw
local notation3 (prettyPrint := false) "physical" => (B raw).owned.symm ⟨q.val.val,q.val.property,rfl⟩
local notation3 (prettyPrint := false) "family" => ownedHistory sa.cube (pub z.1) (mac z.1)
  (fun u => ((B raw).constants u).val.2.1) (fun u => ((B raw).constants u).val.2.2) physical
local notation3 (prettyPrint := false) "visited" => fun u =>
  (visitsEquiv sa.id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)

local notation3 (prettyPrint := false) "data" => bankData q.val.val.2 sa.cube.header.packetBase sa.cube.singleBank
local notation3 (prettyPrint := false) "numbering" => Fin.valEmbedding ∘ owners q.val.val.1

variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)}
    {group : Fin sa.cube.header.d → Fin (R+1)} {frame : ℕ} {guess : Fin (R+1) → ℕ → Bool}
    {dst ib hb sb : Fin (R+1) → ℕ}
    {epoch : ∀ x u, Returns epochPlacement (pub x u) (mac x u) (reg x u) (mem x u)}
    {published : ∀ x u, Returns Packing.Directory.ISA.program (pub x u) (mac x u)
      (epoch x u).val.2.1 (epoch x u).val.2.2}
    {endReg : HeaderExterior L header → Fin (R+1) → Bank w} {out : HeaderExterior L header → Fin (R+1) → Memory w}
    {events : HeaderExterior L header → Fin (R+1) → List (TeamRAM.Event w)}
    {W : ∀ x u, WriterHistory sa.cube.n (selectorWidth sa.cube.n sa.cube.K sa.cube.h) (pub x u) (mac x u)
      (published x u).val.2.1 (published x u).val.2.2 (events x u) (endReg x u) (out x u)}
    (reference : PreparationFrame.WriterProjection G L sa.cube D pp lp owner decl group frame header pin guess dst ib hb sb
      pub mac reg mem epoch published endReg out events W F)

include reference in
/-- At the route returned by the joint inverse, the genuine frozen boot of
this team supplies the descriptor and ID pointers for the owned deck. Its
branch and low memory are the ones used by the actual reference writer. -/
theorem PreparationFrame.sourceEquiv_boot_lookup
    (template : Frame) (slots : ℕ) {teams : Fin (R+1) → TeamHistory w}
    (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner F.origin F.stride
      teams (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u)))
    (writer : SharedWriters f F.rows (F.source z.1)) (rows : f.receivedRows F.rows F.group=(raw).val)
    (handoff : OwnedHandoff f F.rows (F.source z.1) sa.cube decl F.group template sa.id slots family)
    (groupMap : F.group = owners q.val.val.1)
    (u : Fin (R+1)) (demand : ℕ)
    (A : StartupArena)
    (emitted : ReturnedWriters sa.cube D pp lp owner decl group (G.pinLayout u (ib u) (hb u) (sb u)) (W z.1 u))
    {gen : Fragment IO} (hardware : Fin (R+1) → Bank w) (args : Fin (R+1) → UnitAddresses)
    (boot : BootedPinStart gen G (pub z.1) hardware args pin z.1.val u)
    (sub : Fin (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).guessWidth → Bool)
    (memAt : mem z.1 u=(boot.pins sub).val.2.2)
    (head : (pub z.1 u 0).val=A.frame) (row : (args u).ibase=A.ibase) (col : (args u).hbase=A.hbase)
    (old : Fin 81 → Word w) (claimBase who subtotal : ℕ)
    (stored : ∀ j : Fin 81, j.val ∈ [14,40,49,52,53,16,48,50,51] →
      boot.memory ((pub z.1 u 0).val+31+j.val)=sa.extension claimBase who subtotal old j)
    {o clock fresh dest : ℕ} {output : Fin o → ℕ} {trace : List (TeamRAM.Event w)} {after : Bank w} {geo : Memory w}
    (geometry : GeometryReturn (pub z.1 u) (mac z.1 u) (reg z.1 u) (mem z.1 u) fresh dest clock output trace after geo)
    (sourceRoom : A.next ≤ fresh) (outputRoom : A.next ≤ dest)
    {edgeCap cellCap gap : ℕ}
    (placement : (Packing.RoutingOutputs.privateLayout A.frame dest edgeCap cellCap D.entries D.description gap).Image
      (readings geo) D.entries (readings (epoch z.1 u).val.2.2))
    (publishedAt : (published z.1 u).val.2.2=Packing.Directory.ISA.publish (epoch z.1 u).val.2.2 A.frame A.next
      (D.directory pp lp))
    (room : sa.after.packed ≤ 2^w)
    (secondary : A.next ≤ sa.cube.header.header)
    (capacity : (CubeVisits.teamList (data).axis sa.cube.header.blocks numbering u.val).length ≤
      sa.p.report.vertices)
    (width : argumentWidth sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s ≤ sa.p.report.cubeWidth) :
    CubePacket.WordPrepared (gadgetLookup sa (pub full.1 u) numbering u.val demand data)
      sa.id (pub full.1 u) (visited u).owned.val.2.2 := by
  have ptr := reference.sourceBootLookup sa z.1 u A emitted hardware args boot sub memAt head row col old
    claimBase who subtotal (CubeVisits.teamList (data).axis sa.cube.header.blocks numbering u.val).length stored
    geometry sourceRoom outputRoom placement publishedAt room secondary
  exact F.sourceEquiv_owned_lookup sa fixed S B agree q reports template slots f writer rows handoff groupMap u
    demand ptr room capacity width

end TeamContraction

end BorderVNP
end Computability
end OAI
