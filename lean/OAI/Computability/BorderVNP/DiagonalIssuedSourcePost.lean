import OAI.Computability.BorderVNP.DiagonalJointScheduledPost
import OAI.Computability.BorderVNP.DiagonalBootLookupOwnership

/-! # The joint raw prefix's issued argument, complete post and retained reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP VPVNP.BurstRAM FiniteEvaluator DiagonalTallyAllocation DiagonalTallyCellReports
open DiagonalTallyRAM DiagonalTallyMaterialize BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Physical
open BorderVNP.Cube.Padding.Banks TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader
open TeamContraction.JointHeader.PositiveFields ScheduleClock Crossing TeamScales CellPacketGeometry
open RoutingISA.Transmission RoutingISA.CompactMachine CellMacro.Generator Diagonal.Layout
open Diagonal.ExternalSew.Fragments Routing Cube.Scatter Cube.TeamRows Cube.Scatter.Assignment
open DiagonalTallyPacketEmit SignedTaskArena
open scoped Classical
set_option quotPrecheck false
set_option maxHeartbeats 3200000
set_option maxRecDepth 6500

variable {w R n : ℕ} (a : SignedTaskArena.Layout) (U : Fin (R+1) → PinStart SparseExterior.driver n w)
    (active : JointPrefix a.id U) (teamCount : a.cube.teams=R+1) (teamSlot : Fin (R+1))
    (offsets ctl live ports : ℕ)
local notation3 (prettyPrint := false) "asTeam" => Fin.cast teamCount.symm teamSlot
local notation3 (prettyPrint := false) "pub" => (U teamSlot).pub
local notation3 (prettyPrint := false) "mac" => install SparseExterior.driver n (U teamSlot).routines
local notation3 (prettyPrint := false) "V" => visits a.id U (active teamSlot)

variable {r sites pins link inner : ℕ} {Edge : Type} {G : Wiring R r sites pins link inner n Edge}
    {livePin : Fin pins → Bool} {wire : WireLayout (R+1) r link} {common : List Bool}
    {publicAt : HeaderExterior wire common → Fin (R+1) → Arg → Word w}
    {macroAt : HeaderExterior wire common → Fin (R+1) → TeamOpcode.Macros w 8}
    {regsAt : HeaderExterior wire common → Fin (R+1) → Bank w}
    {memoryAt : HeaderExterior wire common → Fin (R+1) → Memory w}
    {decl : LengthDeclaration a.cube.n a.cube.header.d}
    (F : PreparationFrame G wire a.cube decl common livePin publicAt macroAt regsAt memoryAt)
    (seen : HeaderExterior wire common) (ext : Exterior R r link → Bool)
    {owners : (Packet a.cube.n a.cube.header.d a.cube.header.blocks →
      Selector a.cube.n a.cube.K a.cube.h) → Fin a.cube.header.d → Fin (R+1)}
    {template : DiagonalTallyPacketEmit.Frame} {rows : ℕ} (route : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) owners)
    (atOwned : F.ReturnedOwnershipAt a seen ext template rows route (ownedVisits (ar:=a.cube) U active))

local notation3 (prettyPrint := false) "owner" => Fin.valEmbedding ∘ owners route.1
local notation3 (prettyPrint := false) "A" => bankData route.2 a.cube.header.packetBase a.cube.singleBank
local notation3 (prettyPrint := false) "ctrl" => a.controlRows teamSlot.val ((pub 0).val) offsets ctl live ports
local notation3 (prettyPrint := false) "parts" => (argumentVisitsEquiv pub mac (V).reports.val.2.1 (V).reports.val.2.2).symm (V).arguments
local notation3 (prettyPrint := false) "weights" => LocalRow.weightLayout a.cube (pub 0).val decl.1.val
local notation3 (prettyPrint := false) "teams" => LocalRow.teamLayout a.cube R

variable {Site E I Operand P : Type} [Fintype P] [Fintype Operand] {description wp wd bits : ℕ}
    {label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d}
    {recv : Operand → Fin a.cube.cells} {incoming : Operand → ℕ} {routed : ℕ → ℕ} {f : FragmentRows.Layout}
    {bundles b : ℕ} (bundleOwner : Fin bundles → Fin a.cube.cells)
    (bundleHeader : Fin bundles → Packing.BottomReports.BundleHeader)
local notation3 (prettyPrint := false) "H" => a.openInputs teamSlot.val (pub 0).val offsets ctl live ports bundles b bundleOwner bundleHeader

include teamCount atOwned in
/-- Eliminate the one physical launch at this joint prefix only once. Its
elected RAM, sparse source, proposed rows and prepared submitted scanner work
remain tied together all the way to the argument and post-call clocks. -/
theorem post_on_issued_sources {q : ReportCursor} (axis : Fin (a.cube.n+1))
    (selected : owners route.1 = greedyOwner (blocks:=a.cube.header.blocks) (K:=a.cube.K) (h:=a.cube.h)
      R a.cube.b a.cube.s label recv incoming route.1)
    (outside : ℕ) (positive : 0<a.cube.h*a.cube.b) (alphabet : 0<a.cube.header.d)
    {physicalLayout : ReportLayout} {atCell : Fin a.cube.cells → ReportCell physicalLayout}
    {original sampled : List (ReportCell physicalLayout)} {emitted : ℕ → CellPacket.Placed Site} {geometry : ℕ → ℕ}
    {extra : ℕ → List CellSparse.Record} {submitted : ℕ → SparseExterior.Owned}
    (argumentBudget : ℕ) {emissionMemory : Memory w} (nativeEmission : emissionMemory=(parts).1.val.2.2)
    (issued : ∃ (profile assigned : ℕ → ℕ) (native : SparseSource a.id U (active teamSlot))
      (S : SparseReportSources Site E I P a.cube decl label recv incoming assigned teamSlot.val description wp wd
        a.cube.teams a.p.parameters bits native.source f routed ctrl (readings emissionMemory)),
      GroupWeights.ScheduleResult weights teams profile assigned ∧
      GroupWeights.PhysicalImage weights profile a.cube.header.blocks a.cube.b a.cube.K a.cube.h decl label recv incoming ∧
      (TeamBudget.Layout.mk (R+1) outside (teams).totals).Passes assigned ∧
      ProducedRoster a ctrl (readings emissionMemory) S.places S.geometry S.extra native.source ∧
      PreparedReportInput pub (V).controls.val.2.2 (S.reportRows (team:=teamSlot)) q description ∧
      S.LocalReadback (team:=teamSlot) geometry emitted extra submitted atCell original sampled ∧
      traceCost (afterRoute a.id U (active teamSlot)).val.1+
        privateDirectoryTicks pub (afterRoute a.id U (active teamSlot)).val.2.2 ≤ argumentBudget)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter (pub 0).val ctl axis) physicalLayout original q)
    (demand : ℕ)
    (pointers : ∀ i, LookupPointers (a.lookupFrame i) a.after.ids (pub 0).val (F.source seen teamSlot))
    (openPlace : OpenSuffix.Placement H a.cube a.before (pub 0).val (readings (V).owned.val.2.2))
    (openReady : OpenSuffix.Ready H (pub 0).val (readings (V).owned.val.2.2) w)
    (zero : physicalLayout.zeroAddr=a.cube.stop) (width : physicalLayout.countWidth≤w)
    (marked : ∀ c∈original, ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<2^w ∧ p.place<w)
    (reported : IssuedReportFrame a pub (V).reports.val.2.2 offsets ctl (F.dataDir.directory F.privatePlacement F.livePlacement).length)
    (directoryRoom : (F.dataDir.directory F.privatePlacement F.livePlacement).length ≤ a.cube.maxRows)
    {reserve axes groups cap subt u v k : ℕ} (startup : StartupArena)
    (addresses : a.FinishAddresses startup ctl reserve axes groups cap subt w u v k)
    (fields : PositiveFields reserve axes groups cap a.cube.teams a.dim subt)
    (headEq : (pub 0).val=startup.frame)
    (layout : physicalLayout.parameters=a.p.parameters ∧ physicalLayout.gadgets=a.p.report.gadgets)
    {boot : Memory w} {entries indices : ℕ}
    (protectedBanks : ReaderKept startup entries indices boot ((U teamSlot).pins (active teamSlot).1).val.2.2
      (V).owned.val.2.2 ∧ HeaderSeed a fields pub (rawAddress startup reserve axes groups cap) teamSlot.val (V).owned.val.2.2)
    (readerCopied : entries*w≤ startup.copied) (readerIndices : indices≤ startup.count)
    {batch length logPower readerTicks : ℕ} {α ξ : ℝ}
    (windows : a.FinishWindows batch w wp wd bits outside
      ⌈publicWork (a.cube.n+1) α batch length (R+1)⌉₊
      ⌈localWork (a.cube.n+1) logPower α ξ batch length (R+1)⌉₊ readerTicks) :
    let publicCost := ⌈publicWork (a.cube.n+1) α batch length (R+1)⌉₊
    let localCost := ⌈localWork (a.cube.n+1) logPower α ξ batch length (R+1)⌉₊
    let gateCost := cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
      (argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s)
    let rowCost := TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
    traceCost (afterRoute a.id U (active teamSlot)).val.1+
      privateDirectoryTicks pub (afterRoute a.id U (active teamSlot)).val.2.2 ≤ argumentBudget ∧
      ReaderKept startup entries indices boot ((U teamSlot).pins (active teamSlot).1).val.2.2 (active teamSlot).2.val.2.2 ∧
        ∀ (call : Returns callOwnedCells pub mac (active teamSlot).2.val.2.1 (active teamSlot).2.val.2.2)
          (z : Returns (finishExpansion signedOccurrences) pub mac call.val.2.1 call.val.2.2),
        Nonempty (PinStart.PhysicalPost (d:=a.dim) (width:=subt) teamSlot a publicCost localCost gateCost rowCost
          pub mac call.val.2.1 call.val.2.2 z) := by
  subst emissionMemory
  intro publicCost localCost gateCost rowCost
  obtain ⟨_,_,writer,_,owned,observed⟩ := atOwned
  obtain ⟨profile,assigned,native,S,schedule,image,pass,production,seed,readback,charge⟩ := issued
  have produced : ProducedRoster a ctrl (readings (parts).1.val.2.2) emitted geometry extra native.source := by
    rw [←readback.placedEq,←readback.geometryEq,←readback.extraEq]
    exact production
  refine ⟨charge,?_⟩
  exact post_on_launched_joint_prefix a U active teamCount teamSlot offsets ctl live ports writer (F.frame seen)
    owned observed demand native.source S bundleOwner bundleHeader axis schedule image selected outside positive
    alphabet pass readback seed alloc (pointers _) openPlace openReady zero width marked reported directoryRoom produced
    startup addresses fields protectedBanks.2 headEq layout protectedBanks.1 readerCopied readerIndices windows

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
