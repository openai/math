import OAI.Computability.BorderVNP.DiagonalReferenceReaderBanks
import OAI.Computability.BorderVNP.DiagonalReplayPhysicalRows

/-! # The reference writer's reader and header on the reconstructed physical source -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Scatter Scatter.Assignment SignedPrep TeamRows Tally
open DiagonalTallyPacketEmit CellMacro.Generator JointHeader ProcessorSlots SignedTaskArena
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

/-- On the canonical inverse of a declared route and its original report
tapes, read both protected snapshots on the very owned state that the
visits of the actual positive team return. The proof uses the recovered
selector of the concrete delivery, including when the following field
computation is zero. -/
theorem PreparationFrame.sourceEquiv_owned_banks
    (template : Frame) (slots : ℕ) {teams : Fin (R+1) → TeamHistory w}
    (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner F.origin F.stride
      teams (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u)))
    (writer : SharedWriters f F.rows (F.source z.1)) (rows : f.receivedRows F.rows F.group=(raw).val)
    (handoff : OwnedHandoff f F.rows (F.source z.1) sa.cube decl F.group template sa.id slots family)
    (observed : ∃ path, ObservedOwned sa.cube decl F.group family owners (f.receivedRows F.rows F.group) path)
    (A : StartupArena) {entries indices reserve axes groups cap digits : ℕ}
    (fields : PositiveFields reserve axes groups cap sa.cube.teams sa.dim digits)
    (u : Fin (R+1)) (prior boot pinMem : Memory w)
    (source : F.source z.1 u=readings prior)
    (keep : ReaderKept A entries indices boot pinMem prior)
    (seed : HeaderSeed sa fields (pub z.1 u) (rawAddress A reserve axes groups cap) u.val prior)
    (head : (pub z.1 u 0).val=A.frame) (placement : A.next ≤ sa.cube.header.header)
    (packet : entries*w ≤ A.copied) (index : indices ≤ A.count)
    (size : A.header=PositiveFields.width reserve axes groups cap sa.cube.teams sa.dim digits) :
    ReaderKept A entries indices boot pinMem (visited u).owned.val.2.2 ∧
      HeaderSeed sa fields (pub full.1 u) (rawAddress A reserve axes groups cap) u.val (visited u).owned.val.2.2 := by
  let seen (v : Symbols sa.cube.header.d → List Bool) := ∃ a, ObservedOwned sa.cube decl F.group family owners v a
  have exactReceipt := (B raw).observedReceipt physical ((congrArg seen rows).mp observed)
  simp only [Equiv.apply_symm_apply] at exactReceipt
  have actual : ObservedOwned sa.cube decl F.group family owners (f.receivedRows F.rows F.group) q.val.val :=
    (congrArg (fun v => ObservedOwned sa.cube decl F.group family owners v q.val.val) rows).mpr exactReceipt
  have first := writer.returned_reader sa (F.frame z.1) handoff actual u prior source keep head placement packet index
  have second := writer.returned_header_seed sa A fields (F.frame z.1) handoff actual u prior head size placement seed
    (fun j _ => congrFun source j)
  have matchHistory := F.sourceEquiv_owned_history fixed S B agree q reports
  let banks (a : TeamRows.Returns (Fin (R+1)) sa.cube w) := ReaderKept A entries indices boot pinMem (a.output u) ∧
    HeaderSeed sa fields (a.pub u) (rawAddress A reserve axes groups cap) u.val (a.output u)
  exact Eq.mpr (congrArg banks matchHistory) ⟨first,second⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
