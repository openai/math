import OAI.Computability.BorderVNP.DiagonalScheduledVisitFinish
import OAI.Computability.BorderVNP.DiagonalFrozenPrefixFinishCalibration
import OAI.Computability.BorderVNP.DiagonalFrozenPostReportWords
import OAI.Computability.BorderVNP.DiagonalJointVisitCalls
import OAI.Computability.BorderVNP.DiagonalScheduledReportAllocation
import OAI.Computability.BorderVNP.DiagonalSparsePreparedReports
import OAI.Computability.BorderVNP.DiagonalTallyGadgetHandoff
import OAI.Computability.BorderVNP.DiagonalVisitedReaderWords
import OAI.Computability.BorderVNP.DiagonalPhysicalReportSourceWords

/-! # The actual owned lookup, header and sampled scanner in a joint private return -/

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

variable {r t pins link inner : ℕ} {Edge : Type} {G : Wiring R r t pins link inner n Edge}
    {pin : Fin pins → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {placeOwner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {hist : Fin (R+1) → TeamHistory w} {locations : Fin (R+1) → Pins.Layout}
    {f₀ : ReturnedDelivery G pin ext wire D pp lp placeOwner origin stride hist locations}
    {g : SharedRows.Layout} {beforeOwned : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {decl : LengthDeclaration a.cube.n a.cube.header.d} {group : Fin a.cube.header.d → Fin (R+1)}
    {owners : (Packet a.cube.n a.cube.header.d a.cube.header.blocks → Selector a.cube.n a.cube.K a.cube.h) →
      Fin a.cube.header.d → Fin (R+1)} {template : DiagonalTallyPacketEmit.Frame} {rowCount : ℕ}
    (writers : SharedWriters f₀ g beforeOwned)
    (symbols : SymbolFrame g (beforeOwned anchor) a.cube.header.blocks a.cube.K a.cube.h decl group)
    (handoff : OwnedHandoff f₀ g beforeOwned a.cube decl group template a.id rowCount (visitedOwnedScans (ar:=a.cube) (fun i => visits a.id U (active i))))
    {route : NativeAssignments.Routed (b := a.cube.b) (s := a.cube.s) owners}
    (receipt : ObservedOwned a.cube decl group (visitedOwnedScans (ar:=a.cube) (fun i => visits a.id U (active i))) owners (f₀.receivedRows g group) route)
    (demand : ℕ)
local notation3 (prettyPrint := false) "owner" => Fin.valEmbedding ∘ owners route.1
local notation3 (prettyPrint := false) "A" => bankData route.2 a.cube.header.packetBase a.cube.singleBank
local notation3 (prettyPrint := false) "X" => gadgetLookup a pub owner teamSlot.val demand A
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "ctrl" => a.controlRows teamSlot.val head offsets ctl live ports
local notation3 (prettyPrint := false) "parts" => (argumentVisitsEquiv pub mac (V).reports.val.2.1 (V).reports.val.2.2).symm (V).arguments
variable {Site E I Operand P : Type} [Fintype P] [Fintype Operand] {description p d B : ℕ}
    {label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d}
    {recv : Operand → Fin a.cube.cells} {incoming : Operand → ℕ} {assigned : ℕ → ℕ}
    (src : SparseCallInput ((U teamSlot).pub) (sparseMemory a.id U (active teamSlot)))
    {f : FragmentRows.Layout} {routed : ℕ → ℕ}
    (S : SparseReportSources Site E I P a.cube decl label recv incoming assigned teamSlot.val description p d
      a.cube.teams a.p.parameters B src f routed (a.controlRows teamSlot.val ((U teamSlot).pub 0).val offsets ctl live ports)
      (readings ((argumentVisitsEquiv (U teamSlot).pub (install SparseExterior.driver n (U teamSlot).routines)
        (visits a.id U (active teamSlot)).reports.val.2.1 (visits a.id U (active teamSlot)).reports.val.2.2).symm
        (visits a.id U (active teamSlot)).arguments).1.val.2.2))
local notation3 (prettyPrint := false) "rs" => S.reportRows (team := teamSlot)
local notation3 (prettyPrint := false) "L" => S.layout
local notation3 (prettyPrint := false) "weights" => LocalRow.weightLayout a.cube head (A).axis.val
local notation3 (prettyPrint := false) "teams" => LocalRow.teamLayout a.cube R

variable {bundles b : ℕ} (bundleOwner : Fin bundles → Fin a.cube.cells)
    (bundleHeader : Fin bundles → Packing.BottomReports.BundleHeader)
local notation3 (prettyPrint := false) "H" => a.openInputs teamSlot.val head offsets ctl live ports bundles b bundleOwner bundleHeader

include teamCount writers symbols handoff receipt in
/-- The original public writer and owned scan supply the gadget words. The
same sampled-source allocation, protected header and real argument return
then give a bounded private finish for every later successful team return. -/
theorem post_on_received_joint_prefix {q : ReportCursor} (axis : Fin (a.cube.n+1)) {initialMem : ℕ → ℕ}
    (scheduled : GroupWeights.ScheduleResult weights teams initialMem assigned)
    (image : GroupWeights.PhysicalImage weights initialMem a.cube.header.blocks a.cube.b a.cube.K a.cube.h
      decl label recv incoming) (stored : ∀ i : Fin a.cube.header.d, owner i = assigned ((teams).owners+i.val))
    (X₀ : ℕ) (positive : 0<a.cube.h*a.cube.b) (alphabet : 0<a.cube.header.d)
    (pass : (TeamBudget.Layout.mk (R+1) X₀ (teams).totals).Passes assigned)
    (original : List (ReportCell L))
    (seed : PreparedReportInput pub (V).controls.val.2.2 original q description)
    (same : eraseReportBits original=eraseReportBits rs)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) (L) original q)
    (pointers : LookupPointers (a.lookupFrame (X).frame.count) a.after.ids head (beforeOwned teamSlot))
    (openPlace : OpenSuffix.Placement H a.cube a.before head (readings (V).owned.val.2.2))
    (openReady : OpenSuffix.Ready H head (readings (V).owned.val.2.2) w)
    (zero : (L).zeroAddr=a.cube.stop) (width : (L).countWidth≤w)
    (source : ∀ c∈original, ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<2^w ∧ p.place<w)
    (fit : (FragmentRows.Layout.fromFrame head (readings (V).reports.val.2.2)).Fits w (readings (V).reports.val.2.2))
    (pointer : readings (V).reports.val.2.2 (head+92)=ctl)
    (controls : ∀ j : Fin 37, readings (V).reports.val.2.2 (ctl+j.val)=a.controls j.val)
    (nc : (FragmentRows.Layout.fromFrame head (readings (V).reports.val.2.2)).host.count=a.cube.cables)
    (nr : readings (V).reports.val.2.2 (head+9)≤a.cube.maxRows) (cc : readings (V).reports.val.2.2 (head+11)=a.cube.cells)
    (production : ProducedRoster a ctrl (readings (parts).1.val.2.2) S.places S.geometry S.extra src)
    {reserve axes groups hdrCap subt u v k : ℕ} (startup : StartupArena)
    (addresses : a.FinishAddresses startup ctl reserve axes groups hdrCap subt w u v k)
    (fields : PositiveFields reserve axes groups hdrCap a.cube.teams a.dim subt)
    (initial : HeaderSeed a fields pub (rawAddress startup reserve axes groups hdrCap) teamSlot.val (V).owned.val.2.2)
    (headEq : head=startup.frame) (layout : (L).parameters=a.p.parameters ∧ (L).gadgets=a.p.report.gadgets)
    {boot : Memory w} {entries indices : ℕ}
    (readerAtOwned : ReaderKept startup entries indices boot ((U teamSlot).pins (active teamSlot).1).val.2.2 (V).owned.val.2.2)
    (readerCopied : entries*w≤ startup.copied) (readerIndices : indices≤ startup.count)
    {batch length logPower readerTicks : ℕ} {α ξ : ℝ}
    (windows : a.FinishWindows batch w p d B X₀
      ⌈publicWork (a.cube.n+1) α batch length (R+1)⌉₊
      ⌈localWork (a.cube.n+1) logPower α ξ batch length (R+1)⌉₊ readerTicks) :
    let P₀ := ⌈publicWork (a.cube.n+1) α batch length (R+1)⌉₊
    let L₀ := ⌈localWork (a.cube.n+1) logPower α ξ batch length (R+1)⌉₊
    let F := cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
      (argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s)
    let H₀ := TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
    ReaderKept startup entries indices boot ((U teamSlot).pins (active teamSlot).1).val.2.2 (active teamSlot).2.val.2.2 ∧
    ∀ (call : Returns callOwnedCells pub mac (active teamSlot).2.val.2.1 (active teamSlot).2.val.2.2)
      (z : Returns (finishExpansion signedOccurrences) pub mac call.val.2.1 call.val.2.2),
    Nonempty (PinStart.PhysicalPost (d:=a.dim) (width:=subt) teamSlot a P₀ L₀ F H₀
      pub mac call.val.2.1 call.val.2.2 z) := by
  intro P₀ L₀ F H₀
  have place : a.SparsePlacement head ctl := headEq.symm ▸ addresses.place
  have dim : (L).parameters+(L).gadgets≤2^w := by
    rw [layout.1,layout.2]
    exact addresses.reportDim.le
  have vertices : (X).frame.count ≤ a.p.report.vertices :=
    (CubeAllocation.team_count a.cube (A).axis owner teamSlot.val).trans_eq addresses.vertices
  have idsRoom : a.after.packed ≤ 2^w := by
    apply le_trans _ addresses.endFit.le
    dsimp only [Layout.endAddress,Layout.entry,DiagonalResidueRAM.gateBase,Layout.valuation,Layout.tallyBits,
      AfterTasks.localBase,AfterTasks.fresh,AfterTasks.descriptors,AfterTasks.refs]
    omega
  have captured := writers.returned_gadget_lookup a symbols handoff receipt teamSlot demand pointers idsRoom vertices addresses.digitsFit.le
  have prepared := seed.of_same same
  have allocated := alloc.of_same same
  have kept := keptToCalls_on_visits bundleOwner bundleHeader startup V axis openPlace openReady prepared allocated
    place fit pointer controls nc nr cc addresses.endFit addresses.position addresses.controlAbove addresses.geometryAbove S.places S.geometry S.extra src production
  rw [SignedPrep.visitsEquiv_outState] at kept
  have copied := kept.headerSeed fields headEq addresses.headerSize initial
  constructor
  · rw [visits_state a.id U (active teamSlot)]
    have atFrame : KeptToCalls startup startup.frame (V).owned.val.2.2 (V).arguments.val.2.2 := headEq ▸ kept
    exact atFrame.reader readerAtOwned readerCopied readerIndices
  intro call z
  let called := callAtArguments a.id U (active teamSlot) call
  have nativeWindows : a.FinishWindows batch w p d B X₀
      ⌈publicWork (a.cube.n+1) α batch length a.cube.teams⌉₊
      ⌈localWork (a.cube.n+1) logPower α ξ batch length a.cube.teams⌉₊ readerTicks := by
    simpa only [teamCount] using windows
  have finish := physicalPost_on_scheduled_visits (logPower:=logPower) a teamCount asTeam offsets ctl live ports owner demand A V src S
    scheduled image stored X₀ positive alphabet pass prepared allocated captured H openPlace openReady rfl rfl rfl rfl
    zero addresses.wordPos dim width (report_positions_of_same same source) place.primary addresses.sortedHi place.beforeControl addresses.ctlHi place fit pointer controls nc nr cc addresses.endFit production
    startup fields copied headEq layout vertices addresses.digitsFit.le (fun i => (addresses.idFit _).trans_eq layout.2.symm) addresses.headerSize addresses.position
    addresses.teamsFit addresses.widthFit called z nativeWindows
  have actual : Nonempty (PhysicalPost (d:=a.dim) (width:=subt) teamSlot a
      ⌈publicWork (a.cube.n+1) α batch length a.cube.teams⌉₊
      ⌈localWork (a.cube.n+1) logPower α ξ batch length a.cube.teams⌉₊ F H₀
      pub mac call.val.2.1 call.val.2.2 z) :=
    finish.map (fun record => record.reindex teamCount rfl rfl)
  simpa only [P₀,L₀,F,H₀,teamCount] using actual

include teamCount writers symbols handoff receipt in
/-- Join the actually submitted sparse source and original allocation to
the same elected team schedule. The native scanner may have returned any
tape at this prefix. Each team supplies its own physical source readback. -/
theorem post_on_launched_joint_prefix {q : ReportCursor} (axis : Fin (a.cube.n+1)) {initialMem : ℕ → ℕ}
    (scheduled : GroupWeights.ScheduleResult (LocalRow.weightLayout a.cube head decl.1.val) teams initialMem assigned)
    (image : GroupWeights.PhysicalImage (LocalRow.weightLayout a.cube head decl.1.val) initialMem a.cube.header.blocks a.cube.b a.cube.K a.cube.h
      decl label recv incoming) (selected : owners route.1 =
        greedyOwner (blocks:=a.cube.header.blocks) (K:=a.cube.K) (h:=a.cube.h) R a.cube.b a.cube.s label recv incoming route.1)
    (X₀ : ℕ) (positive : 0<a.cube.h*a.cube.b) (alphabet : 0<a.cube.header.d)
    (pass : (TeamBudget.Layout.mk (R+1) X₀ (teams).totals).Passes assigned)
    {physicalLayout : ReportLayout} {atCell : Fin a.cube.cells → ReportCell physicalLayout}
    {original sampled : List (ReportCell physicalLayout)} {sites : ℕ → CellPacket.Placed Site}
    {geometry : ℕ → ℕ} {extra : ℕ → List CellSparse.Record} {submitted : ℕ → SparseExterior.Owned}
    (readback : S.LocalReadback (team:=teamSlot) geometry sites extra submitted atCell original sampled)
    (seeded : PreparedReportInput pub (V).controls.val.2.2 rs q description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) physicalLayout original q)
    (pointers : LookupPointers (a.lookupFrame (X).frame.count) a.after.ids head (beforeOwned teamSlot))
    (openPlace : OpenSuffix.Placement H a.cube a.before head (readings (V).owned.val.2.2))
    (openReady : OpenSuffix.Ready H head (readings (V).owned.val.2.2) w)
    (zero : physicalLayout.zeroAddr=a.cube.stop) (width : physicalLayout.countWidth≤w)
    (source : ∀ c∈original, ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<2^w ∧ p.place<w)
    (reported : IssuedReportFrame a pub (V).reports.val.2.2 offsets ctl (D.directory pp lp).length)
    (directoryRoom : (D.directory pp lp).length ≤ a.cube.maxRows)
    (production : ProducedRoster a ctrl (readings (parts).1.val.2.2) sites geometry extra src)
    {reserve axes groups hdrCap subt u v k : ℕ} (startup : StartupArena)
    (addresses : a.FinishAddresses startup ctl reserve axes groups hdrCap subt w u v k)
    (fields : PositiveFields reserve axes groups hdrCap a.cube.teams a.dim subt)
    (initial : HeaderSeed a fields pub (rawAddress startup reserve axes groups hdrCap) teamSlot.val (V).owned.val.2.2)
    (headEq : head=startup.frame) (layout : physicalLayout.parameters=a.p.parameters ∧ physicalLayout.gadgets=a.p.report.gadgets)
    {boot : Memory w} {entries indices : ℕ}
    (readerAtOwned : ReaderKept startup entries indices boot ((U teamSlot).pins (active teamSlot).1).val.2.2 (V).owned.val.2.2)
    (readerCopied : entries*w≤ startup.copied) (readerIndices : indices≤ startup.count)
    {batch length logPower readerTicks : ℕ} {α ξ : ℝ}
    (windows : a.FinishWindows batch w p d B X₀
      ⌈publicWork (a.cube.n+1) α batch length (R+1)⌉₊
      ⌈localWork (a.cube.n+1) logPower α ξ batch length (R+1)⌉₊ readerTicks) :
    let P₀ := ⌈publicWork (a.cube.n+1) α batch length (R+1)⌉₊
    let L₀ := ⌈localWork (a.cube.n+1) logPower α ξ batch length (R+1)⌉₊
    let F := cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
      (argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s)
    let H₀ := TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
    ReaderKept startup entries indices boot ((U teamSlot).pins (active teamSlot).1).val.2.2 (active teamSlot).2.val.2.2 ∧
    ∀ (call : Returns callOwnedCells pub mac (active teamSlot).2.val.2.1 (active teamSlot).2.val.2.2)
      (z : Returns (finishExpansion signedOccurrences) pub mac call.val.2.1 call.val.2.2),
    Nonempty (PinStart.PhysicalPost (d:=a.dim) (width:=subt) teamSlot a P₀ L₀ F H₀
      pub mac call.val.2.1 call.val.2.2 z) := by
  obtain ⟨fr,_,compacted,_,cells,cables,_,words,sparse⟩ := reported
  obtain ⟨fit,pointer,controls,nc,nr,cc⟩ := fr.postReportWords a compacted cells cables words sparse directoryRoom
  have layoutEq := readback.layoutEq
  subst physicalLayout
  have same : eraseReportBits original=eraseReportBits rs := eq_of_heq readback.same
  have originalSeed := seeded.of_same same.symm
  have production' : ProducedRoster a ctrl (readings (parts).1.val.2.2) S.places S.geometry S.extra src := by
    rw [readback.placedEq,readback.geometryEq,readback.extraEq]
    exact production
  have declaration : Routed.trueDeclaration a.cube.b a.cube.s route.1=decl := receipt.observed.1
  have valid : passesLengths a.cube.b a.cube.s route.1 decl :=
    (passesLengths_iff ..).mpr declaration.symm
  have localAxis : (A).axis=decl.1 := congrArg Prod.fst declaration
  have stored (i : Fin a.cube.header.d) : owner i=assigned ((teams).owners+i.val) := by
    change (owners route.1 i).val=_
    rw [selected]
    exact (greedyOwner_stored scheduled route.1 valid label recv incoming image i).symm
  have elected : GroupWeights.ScheduleResult weights teams initialMem assigned := by rw [localAxis]; exact scheduled
  have physical : GroupWeights.PhysicalImage weights initialMem a.cube.header.blocks a.cube.b a.cube.K a.cube.h
      decl label recv incoming := by rw [localAxis]; exact image
  exact post_on_received_joint_prefix a U active teamCount teamSlot offsets ctl live ports writers symbols handoff receipt
    demand src S bundleOwner bundleHeader axis elected physical stored X₀ positive alphabet pass original originalSeed same
    alloc pointers openPlace openReady zero width source fit pointer controls nc nr cc production' startup addresses fields
    initial headEq layout readerAtOwned readerCopied readerIndices windows

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
