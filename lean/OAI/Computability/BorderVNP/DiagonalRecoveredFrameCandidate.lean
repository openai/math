import OAI.Computability.BorderVNP.DiagonalBootLookupOwnership
import OAI.Computability.BorderVNP.DiagonalPhysicalReportSourceWords

/-! # Retrieving the same arrived candidate along a selected source inverse -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction
open Diagonal.ExternalSew.Fragments

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

/-- Any physical candidate certificate built from the original returned
site, its true writer and its actual owned scanner can be read on the
selected source inverse. The replayed writer here carries all the label,
pin and end-state evidence required by the candidate builder. -/
theorem PreparationFrame.sourceEquiv_recovered_candidate
    (certificate : HeaderExterior L header → NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners →
      TeamRows.Returns (Fin (R+1)) sa.cube w → Prop)
    (reached : ∀ operands : SharedWords sa.cube decl, let source := F.replay fixed operands
      ∀ (H : Fin (R+1) → TeamHistory w)
        (f : ReturnedDelivery G pin source.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
          F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
        f.table=F.tab → f.row=F.row → SharedWriters f F.rows (F.source source.1) →
        (∀ u, (H u).pub=pub source.1 u ∧ (H u).macros=mac source.1 u ∧ (H u).history.val.2=(source.2 u).val.2) →
        (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
          (F.guess u) (H u).initial) → f.receivedRows F.rows F.group=operands.val →
        ∀ (route : Matching sa.cube owners decl (f.receivedRows F.rows F.group))
          (endRows : TeamRows.Returns (Fin (R+1)) sa.cube w),
          OwnedHandoff f F.rows (F.source source.1) sa.cube decl F.group template sa.id slots endRows →
          ObservedOwned sa.cube decl F.group endRows owners (f.receivedRows F.rows F.group) route.val →
          certificate source.1 route.val endRows)
    (common : ∀ u, readings (pub z.1 u) 0=publication.frame)
    (space : sa.after.packed ≤ 2^w) (values : CubeConstants.valueBound sa.id<2^w)
    (room : sa.cube.ReplayRoom w publication.frame)
    (scanner : ∀ u : Fin (R+1), sa.cube.ScannerWords (readings (pub z.1 u) 0) u.val decl.1.val
      (fun j => (F.group j).val) (readings (pub z.1 u)) (F.source z.1 u) decl.2)
    (fields : ∀ u, CubeConstants.Fields pack (readings (pub z.1 u) 0) ids (F.source z.1 u))
    (scheduled : F.group=owners q.val.val.1) :
    certificate full.1 q.val.val (visitedOwnedScans (ar:=sa.cube) (visited)) := by
  obtain ⟨H,f,ft,fr,writer,actual,pins,rows,handoff⟩ :=
    publication.replayedOwnershipFull sa fixed S F B q template common space values room scanner fields
  have seen := F.replay_observed_owned sa fixed S B q template slots f writer rows handoff scheduled
  let matching : Matching sa.cube owners decl (f.receivedRows F.rows F.group) :=
    ⟨q.val.val,q.val.property,rows.symm⟩
  have result := reached raw H f ft fr writer actual pins rows matching family handoff seen
  have exterior : full.1=z.1 := Subtype.ext rfl
  have history := F.sourceEquiv_owned_history fixed S B agree q reports
  exact (congrArg₂ (fun site runs => certificate site q.val.val runs) exterior history).mpr result

end TeamContraction

end BorderVNP
end Computability
end OAI
