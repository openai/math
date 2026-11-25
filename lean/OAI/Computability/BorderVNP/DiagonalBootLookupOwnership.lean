import OAI.Computability.BorderVNP.DiagonalBootLookupInputs
import OAI.Computability.BorderVNP.DiagonalSignedWriterDictionary
import OAI.Computability.BorderVNP.DiagonalBareOwnedHandoff

/-! # The canonical delivery and ownership handoff at a replayed lookup -/

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

/-- The route inverse determines the actual transmitting array, its final
shared data and the installed dictionary at this owned scan. The native
installer in the returned builder proves the handoff on its exact register
and memory states. -/
theorem PreparationFrame.LookupPublication.replayedOwnershipFull
    (common : ∀ u, readings (pub z.1 u) 0=publication.frame)
    (space : sa.after.packed ≤ 2^w) (values : CubeConstants.valueBound sa.id<2^w)
    (room : sa.cube.ReplayRoom w publication.frame)
    (scanner : ∀ u : Fin (R+1), sa.cube.ScannerWords (readings (pub z.1 u) 0) u.val decl.1.val
      (fun j => (F.group j).val) (readings (pub z.1 u)) (F.source z.1 u) decl.2)
    (fields : ∀ u, CubeConstants.Fields pack (readings (pub z.1 u) 0) ids (F.source z.1 u)) :
    ∃ (H : Fin (R+1) → TeamHistory w)
      (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner F.origin F.stride
        H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
      f.table=F.tab ∧ f.row=F.row ∧ SharedWriters f F.rows (F.source z.1) ∧
      (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) ∧
      (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
        (F.guess u) (H u).initial) ∧ f.receivedRows F.rows F.group=(raw).val ∧
      OwnedHandoff f F.rows (F.source z.1) sa.cube decl F.group template sa.id slots family := by
  obtain ⟨H,f,tab,row,writer,actual,pins,rows⟩ := F.replayDelivery fixed raw
  refine ⟨H,f,tab,row,writer,actual,pins,rows,?_⟩
  have commonAt (u : Fin (R+1)) : readings (H u).pub 0=publication.frame := by
    rw [(actual u).1,common u]
  have tableAt (u : Fin (R+1)) : f.table=sa.cube.table (readings (H u).pub 0) slots := by
    rw [commonAt]
    exact tab.trans publication.projection.table
  have roomAt (u : Fin (R+1)) : sa.cube.ReplayRoom w (readings (H u).pub 0) := commonAt u ▸ room
  have fr (u : Fin (R+1)) : F.rows.frame=readings (H u).pub 0 := by
    rw [commonAt,publication.projection.shared]
    rfl
  have fieldsAt (u : Fin (R+1)) : CubeConstants.Fields pack (readings (H u).pub 0) ids (F.source z.1 u) :=
    (actual u).1 ▸ fields u
  have bounds (u : Fin (R+1)) := sa.signed_dictionary_addresses (roomAt u).primary space
  have loaded := writer.signedInstallOnRoute sa.cube template sa.id slots tableAt fieldsAt
    (fun u => (roomAt u).primary) (fun u => (bounds u).1) fr (bounds 0).2 values
  refine ⟨fun u => (actual u).1.symm,fun u => (actual u).2.1.symm,?_,?_,roomAt,tableAt,fr,?_,
    fun u => (loaded u).1,fun u => (loaded u).2.1,?_⟩
  · rw [publication.projection.shared]
    rfl
  · rw [publication.projection.shared]
    rfl
  · intro u
    rw [(actual u).1]
    exact scanner u
  · intro u
    refine ⟨((B raw).constants u).val.1,?_⟩
    exact runAt (actual u).1.symm (actual u).2.1.symm (actual u).2.2.symm ((B raw).constants u).property

/-- The returned writer and its installed constant deck on the recovered
ownership, with the same replayer and route. -/
theorem PreparationFrame.LookupPublication.replayedOwnership
    (common : ∀ u, readings (pub z.1 u) 0=publication.frame)
    (space : sa.after.packed ≤ 2^w) (values : CubeConstants.valueBound sa.id<2^w)
    (room : sa.cube.ReplayRoom w publication.frame)
    (scanner : ∀ u : Fin (R+1), sa.cube.ScannerWords (readings (pub z.1 u) 0) u.val decl.1.val
      (fun j => (F.group j).val) (readings (pub z.1 u)) (F.source z.1 u) decl.2)
    (fields : ∀ u, CubeConstants.Fields pack (readings (pub z.1 u) 0) ids (F.source z.1 u)) :
    ∃ (H : Fin (R+1) → TeamHistory w)
      (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner F.origin F.stride
        H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
      SharedWriters f F.rows (F.source z.1) ∧ f.receivedRows F.rows F.group=(raw).val ∧
      OwnedHandoff f F.rows (F.source z.1) sa.cube decl F.group template sa.id slots family := by
  obtain ⟨H,f,_,_,writer,_,_,rows,handoff⟩ :=
    publication.replayedOwnershipFull sa fixed S F B q template common space values room scanner fields
  exact ⟨H,f,writer,rows,handoff⟩

/-- A returned transmission carrying the proposed shared route and passing
its physically installed dictionary to the specified family of owned scans. -/
def PreparationFrame.ReturnedOwnershipAt (origin : HeaderExterior L header)
    (exterior : Exterior R r link → Bool) (template₀ : Frame) (count : ℕ)
    (v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners)
    (run : TeamRows.Returns (Fin (R+1)) sa.cube w) : Prop :=
  ∃ (H : Fin (R+1) → TeamHistory w)
    (f : ReturnedDelivery G pin exterior L F.dataDir F.privatePlacement F.livePlacement F.cellOwner F.origin F.stride
      H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
    SharedWriters f F.rows (F.source origin) ∧ f.receivedRows F.rows F.group=(Routed.encode owners v).shared ∧
    OwnedHandoff f F.rows (F.source origin) sa.cube decl F.group template₀ sa.id count run ∧
    ObservedOwned sa.cube decl F.group run owners (f.receivedRows F.rows F.group) v

/-- The delivery and the ownership readback arise on the same replay and
the same installer. Its full public rows and owned route are both retained. -/
theorem PreparationFrame.LookupPublication.replayedOwnershipAt
    (common : ∀ u, readings (pub z.1 u) 0=publication.frame)
    (space : sa.after.packed ≤ 2^w) (values : CubeConstants.valueBound sa.id<2^w)
    (room : sa.cube.ReplayRoom w publication.frame)
    (words : ∀ u : Fin (R+1), SharedCubeWords sa decl F.group u.val (readings (pub z.1 u)) (F.source z.1 u) entries)
    (groups : F.group=owners q.val.val.1) : F.ReturnedOwnershipAt sa z.1 z.1.val template slots q.val.val family := by
  obtain ⟨H,f,writes,rows,pass⟩ := publication.replayedOwnership sa fixed S F B q template
    common space values room (fun u => (words u).scanner) (fun u => (words u).fields template)
  exact ⟨H,f,writes,rows,pass,F.replay_observed_owned sa fixed S B q template slots f writes rows pass groups⟩

/-- Complete the frozen startup's lookup input using the decoded source
delivery and the table fields of its native schedule. The resulting lookup
reuses the given local boot and the installed arena. -/
noncomputable def PreparationFrame.LookupStartup.withOwnership {u : Fin (R+1)}
    (boot : F.LookupStartup sa fixed S q u)
    (common : ∀ v, readings (pub z.1 v) 0=boot.publication.frame)
    (values : CubeConstants.valueBound sa.id<2^w) (room : sa.cube.ReplayRoom w boot.publication.frame)
    (scanner : ∀ v : Fin (R+1), sa.cube.ScannerWords (readings (pub z.1 v) 0) v.val decl.1.val
      (fun j => (F.group j).val) (readings (pub z.1 v)) (F.source z.1 v) decl.2)
    (fields : ∀ v, CubeConstants.Fields pack (readings (pub z.1 v) 0) ids (F.source z.1 v))
    (groups : F.group=owners q.val.val.1) : F.BootLookupAt sa fixed S B q u := by
  let e := boot.publication.replayedOwnership sa fixed S F B q template common boot.room values room scanner fields
  exact ⟨boot,template,_,e.choose,e.choose_spec.choose,e.choose_spec.choose_spec.1,
    e.choose_spec.choose_spec.2.1,e.choose_spec.choose_spec.2.2,groups⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
