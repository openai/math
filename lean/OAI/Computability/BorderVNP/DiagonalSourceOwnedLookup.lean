import OAI.Computability.BorderVNP.DiagonalTallyGadgetHandoff
import OAI.Computability.BorderVNP.DiagonalReplayPhysicalRows
import OAI.Computability.BorderVNP.DiagonalSourceOwnedReceipt
import OAI.Computability.BorderVNP.DiagonalPrivatePathRead
import OAI.Computability.BorderVNP.CubePhysicalSignedVisitOrder

/-! # Reading the selected gadget deck at the actual source-owned return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.Inherited Packing.Inherited.Placement
open Scatter.Assignment Diagonal.CellEntries
open scoped Classical

variable {D ne n d blocks b h K s : ℕ} {P Cell Team : Type} [Fintype P] [DecidableEq Cell]
  {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Cell) (edge : N.Edge ↪ Fin ne)
  (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
  (q : Routed (b:=b) (s:=s) owners)

omit [DecidableEq Cell] in
/-- The three physical payload arrays of the recovered path are exactly the
ones installed by the routed tape, at both native base addresses. -/
theorem rawPath_banks (bank : (c : Cell) → Fin (externalBase N cell c (placedSize N state)) → Bool)
    (packet single : ℕ) :
    NativeLedger.pathBanks (rawPath N cell edge state owners q bank) packet single =
      bankData q.2 packet single := rfl

end Cube.Physical.NativeAssignments

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Scatter Scatter.Assignment SignedPrep TeamRows Tally
open DiagonalTallyPacketEmit CellMacro.Generator JointHeader ProcessorSlots SignedTaskArena FiniteEvaluator
open private recover_decoded from OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily
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

private theorem declared_shared_image
    (v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners)
    (D : LengthDeclaration sa.cube.n sa.cube.header.d)
    (h : Routed.trueDeclaration sa.cube.b sa.cube.s v.1 = D) :
    let a : DeclaredShared sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.K sa.cube.s D :=
      h ▸ Routed.physicalShared owners v
    sharedWords D a=(Routed.encode owners v).shared ∧ a.1.val=v.1 := by
  subst D
  exact ⟨(Routed.encode_shared owners v).symm,rfl⟩

/-- Decode the public selector once and recover this very original assignment
from the replayed writer and its installed ownership scan. -/
theorem PreparationFrame.replay_observed_owned
    (template : Frame) (slots : ℕ) {teams : Fin (R+1) → TeamHistory w}
    (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner F.origin F.stride
      teams (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u)))
    (writer : SharedWriters f F.rows (F.source z.1)) (rows : f.receivedRows F.rows F.group=(raw).val)
    (handoff : OwnedHandoff f F.rows (F.source z.1) sa.cube decl F.group template sa.id slots family)
    (groupMap : F.group = owners q.val.val.1)
    : ObservedOwned sa.cube decl F.group family owners (f.receivedRows F.rows F.group) q.val.val := by
  have observed : ∃ path, ObservedOwned sa.cube decl F.group family owners (f.receivedRows F.rows F.group) path := by
    let q₀ := q.val.val
    have declEq : Routed.trueDeclaration sa.cube.b sa.cube.s q₀.1 = decl := q.val.property
    let transported : DeclaredShared sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.K sa.cube.s decl :=
      declEq ▸ Routed.physicalShared owners q₀
    have restored := declared_shared_image sa q₀ decl declEq
    exact (recover_decoded sa.cube decl F.group family owners writer (F.frame z.1) handoff transported
      (restored.1.trans rows.symm) (groupMap.trans (congrArg owners restored.2.symm))).exists
  let seen (v : Symbols sa.cube.header.d → List Bool) := ∃ a, ObservedOwned sa.cube decl F.group family owners v a
  have exactReceipt := (B raw).observedReceipt physical ((congrArg seen rows).mp observed)
  simp only [Equiv.apply_symm_apply] at exactReceipt
  have actual : ObservedOwned sa.cube decl F.group family owners (f.receivedRows F.rows F.group) q.val.val :=
    (congrArg (fun v => ObservedOwned sa.cube decl F.group family owners v q.val.val) rows).mpr exactReceipt
  exact actual

/-- The live register bank and memory in the reconstructed ownership segment
carry the gadget IDs of the declared route, for arbitrary original report
guesses. The owner and packet lookups use the same routing witness. -/
theorem PreparationFrame.sourceEquiv_owned_lookup
    (template : Frame) (slots : ℕ) {teams : Fin (R+1) → TeamHistory w}
    (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner F.origin F.stride
      teams (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u)))
    (writer : SharedWriters f F.rows (F.source z.1)) (rows : f.receivedRows F.rows F.group=(raw).val)
    (handoff : OwnedHandoff f F.rows (F.source z.1) sa.cube decl F.group template sa.id slots family)
    (groupMap : F.group = owners q.val.val.1)
    (u : Fin (R+1)) (demand : ℕ)
    (ptr : LookupPointers
      (sa.lookupFrame (CubeVisits.teamList (data).axis sa.cube.header.blocks numbering u.val).length)
      sa.after.ids (readings (pub z.1 u) 0) (F.source z.1 u))
    (room : sa.after.packed ≤ 2^w)
    (capacity : (CubeVisits.teamList (data).axis sa.cube.header.blocks numbering u.val).length ≤
      sa.p.report.vertices)
    (width : argumentWidth sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s ≤ sa.p.report.cubeWidth) :
    CubePacket.WordPrepared (gadgetLookup sa (pub full.1 u) numbering u.val demand data)
      sa.id (pub full.1 u) (visited u).owned.val.2.2 := by
  have actual := F.replay_observed_owned sa fixed S B q template slots f writer rows handoff groupMap
  have deck := writer.returned_gadget_lookup sa (F.frame z.1) handoff actual u demand ptr room capacity width
  have same := F.sourceEquiv_owned_history fixed S B agree q reports
  let good (a : TeamRows.Returns (Fin (R+1)) sa.cube w) :=
    CubePacket.WordPrepared (gadgetLookup sa (a.pub u) numbering u.val demand data) sa.id (a.pub u) (a.output u)
  exact Eq.mpr (congrArg good same) deck

end TeamContraction

end BorderVNP
end Computability
end OAI
