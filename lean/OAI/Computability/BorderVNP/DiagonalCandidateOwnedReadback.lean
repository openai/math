import OAI.Computability.BorderVNP.DiagonalCandidateSignedBootReadback
import OAI.Computability.BorderVNP.DiagonalBootLookupOwnership
import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderRoute

/-! # The owned lookup and copied subtotal from the candidate's actual signed publisher -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace TeamContraction

open private runAt from OAI.Computability.BorderVNP.DiagonalBareOwnedHandoff
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

variable (publication : F.LookupPublication sa) (template : Frame)
local notation3 (prettyPrint := false) "entries" =>
  (publication.directory.directory publication.privatePlacement publication.livePlacement).length
local notation3 (prettyPrint := false) "slots" => entries+sa.cube.header.d.choose 2
local notation3 (prettyPrint := false) "pack" =>
  CubeConstants.inArena template sa.cube.stop sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s
local notation3 (prettyPrint := false) "ids" =>
  CubeConstants.idBase sa.cube.stop sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s

open PackedHistoryCircuit LocalRow Crossing

include template in
/-- The recovered shared transmission installs the lookup deck and preserves the
subtotal of the chosen candidate on its very same owned return. All private
report guesses use the one public candidate writer and the original signed
packet. -/
theorem PreparationFrame.sourceEquiv_candidateOwnedReadback
    {X : ℕ} {D₀ : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {word : Broadcast sa.cube.n sa.cube.header.d sa.cube.header.cap} {representative : ℕ → Fin (R+1)}
    {group₀ : Fin sa.cube.header.d → Fin (R+1)} {base₀ receiving : ℕ} {pins₀ : Pins.Layout}
    {fields₀ : Pins.ProcessorFields pins₀} {copy : BroadcastFrame} {guess : ℕ → Bool}
    {I : Type*} [Fintype I] {host : I → Fin sa.cube.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {depth : ℕ} {P A : Type*} {bits : P → ℕ} {N : Crossing.Network depth P bits} {cell : N.Site → Fin sa.cube.cells}
    {recv : A → Fin sa.cube.cells} {amount : A → ℕ} (u : Fin (R+1))
    (candidate : CandidateSite (X:=X) sa.cube D₀ pp lp word representative decl group₀ base₀ receiving
      pins₀ fields₀ copy guess (pub z.1 u) (mac z.1 u) (reg z.1 u) (mem z.1 u) host key sizes N cell recv amount)
    (sourceRAM : F.source z.1 u=readings candidate.receipt.history.sharedInput)
    (A₀ : StartupArena) {res side blocks cap hdrWidth : ℕ}
    (packet : PositiveFields res side blocks cap sa.cube.teams sa.dim hdrWidth) (previous : Fin 81 → Word w)
    (origin : ℕ)
    (signed : candidate.old=routingExtension (sa.extension (rawAddress A₀ res side blocks cap) u.val hdrWidth previous)
      D₀ origin sa.cube.cables sa.cube.cells)
    (bitsRead : padded (spelling (candidate.profile++DeclarationBits.spelling word) candidate.claims)
      candidate.pad=packet.bits)
    (head : (pub z.1 u 0).val=A₀.frame) (dest : copy.dst=A₀.broadcastBase)
    (size : A₀.header=PositiveFields.width res side blocks cap sa.cube.teams sa.dim hdrWidth)
    (secondary : A₀.next ≤ sa.cube.header.header) {query guesses gates : ℕ}
    (endFit : sa.endAddress w query guesses gates<2^w) (teamCount : sa.cube.teams=R+1)
    (teamsFit : sa.cube.teams<2^w) (widthFit : hdrWidth≤w) (wordPos : 0<w)
    (common : ∀ v,readings (pub z.1 v) 0=publication.frame)
    (room : sa.after.packed ≤ 2^w) (values : CubeConstants.valueBound sa.id<2^w)
    (replayRoom : sa.cube.ReplayRoom w publication.frame)
    (words : ∀ v : Fin (R+1), SharedCubeWords sa decl F.group v.val (readings (pub z.1 v)) (F.source z.1 v) entries)
    (scheduled : F.group=owners q.val.val.1) (demand : ℕ)
    (capacity : (CubeVisits.teamList (data).axis sa.cube.header.blocks numbering u.val).length ≤ sa.p.report.vertices)
    (digitsFit : Tally.argumentWidth sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s ≤ sa.p.report.cubeWidth) :
    (pub full.1 u 0).val=A₀.frame ∧
      CubePacket.WordPrepared (gadgetLookup sa (pub full.1 u) numbering u.val demand data)
        sa.id (pub full.1 u) (visited u).owned.val.2.2 ∧
      HeaderSeed sa packet (pub full.1 u) (rawAddress A₀ res side blocks cap) u.val (visited u).owned.val.2.2 := by
  obtain ⟨H,f,writer,rows,handoff⟩ := publication.replayedOwnership sa fixed S F B q template common room values
    replayRoom (fun v => (words v).scanner) (fun v => (words v).fields template)
  have receipt := F.replay_observed_owned sa fixed S B q template slots f writer rows handoff scheduled
  have seed := candidate.sharedHeaderSeed sa A₀ packet previous origin u.val signed bitsRead head dest size secondary
    endFit teamsFit (by rw [teamCount]; exact u.isLt) widthFit wordPos
  have copied := writer.returned_header_seed sa A₀ packet (F.frame z.1) handoff receipt u
    candidate.receipt.history.sharedInput head size secondary seed (fun j _ => congrFun sourceRAM j)
  have deck := writer.returned_gadget_lookup sa (F.frame z.1) handoff receipt u demand ((words u).lookup _)
    room capacity digitsFit
  let ok (fam : TeamRows.Returns (Fin (R+1)) sa.cube w) :=
    (fam.pub u 0).val=A₀.frame ∧ CubePacket.WordPrepared (gadgetLookup sa (fam.pub u) numbering u.val demand data)
      sa.id (fam.pub u) (fam.output u) ∧ HeaderSeed sa packet (fam.pub u)
      (rawAddress A₀ res side blocks cap) u.val (fam.output u)
  exact (congrArg ok (F.sourceEquiv_owned_history fixed S B agree q reports)).mpr ⟨head,deck,copied⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
