import OAI.Hierarchy.TaggedWideSignedMeasuredPair
import OAI.Hierarchy.ProbeFixedWideSignedControlFields
import OAI.Hierarchy.TaggedWideFundedSelectedPacket
import OAI.Hierarchy.ProbeFixedFundedLowTable
import OAI.Hierarchy.TaggedWideSelectedSignedNeighbors
import OAI.Hierarchy.TaggedWideFundedIndexedReplay
import OAI.Hierarchy.ProbeFixedFundedPartyTag
import OAI.Hierarchy.ProbeFixedFundedOccupiedRows

namespace OAI
/-! # The selected vote is read from its own native processing snapshot -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open TaggedPrune Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unitCost g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
    (v.wide_dated_sites h width ell unitCost) (v.wide_dated_edges h width ell unitCost) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
variable (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
variable {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)
local notation "report" => v.wide_reported_path h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
    Sfit support.size.late support.size.words j
local notation "bought" => v.wide_selected_local_return m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "rootROM" => v.wideInstalledRoot x
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
local notation "rankEnd" => v.wideSpillRankEnd h width v.maxBits first
variable (side : Bool) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "chosen" => WireTelescope.CalendarTape.Prefix.pathVisitAt j t onDate
local notation "date" => v.wide_funded_date_with h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior (chosen).choice (chosen).future
local notation "reference" => v.wide_reference_date h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior
local notation "window" => (reader).format.windows
local notation "record" => CalendarTape.encode sl es base j
local notation "chart" => v.wideSignedChart h width (v.fixedTerminalStock (v.widePlacement h width) h width)
open Lean Elab Term Meta in
local elab "lowPacketAt% " head:ident "[" operands:term,* "]" : term => do
  let args ← operands.getElems.mapM (fun operand => elabTerm operand none)
  let c ← resolveGlobalConstNoOverload head
  return mkAppN (← mkConstWithFreshMVarLevels c) args

open Lean Elab Term Meta in
local elab "lowRateOf% " v:ident : term => do
  let actual ← getFVarFromUserName v.getId
  let type ← inferType actual
  let some format ← whnfUntil type ``FixedProtocolFormat | throwError "missing funded format"
  return format.getAppArgs[4]!
open Lean Elab Term Meta in
local elab "lowCountsOf% " e:ident : term => do
  let actual ← getFVarFromUserName e.getId
  let type ← whnf (← inferType actual)
  unless type.isForall do throwError "missing elected input"
  let some pins ← whnfUntil type.bindingDomain! ``OpenPins | throwError "missing funded pins"
  return pins.getAppArgs.back!
local notation "memo" => lowPacketAt% wide_selected_ballot_snapshots [F,(inferInstance : Field F),k,p,(lowRateOf% v),Q,σ,Λ,κ,A,v,m,ell,short,u,δ,ξ,unitCost,N,x,cpu,rate,support,prices,C,pricePos,buy,groupsFit,metadata,lanesFit,(lowCountsOf% e),e,perm,tag,j,side,t,a,onDate]
local notation "issuedFacts" => lowPacketAt% wide_selected_packet_reads [F,(inferInstance : Field F),k,p,(lowRateOf% v),Q,σ,Λ,κ,A,v,m,ell,short,u,δ,ξ,unitCost,N,x,cpu,rate,support,prices,C,pricePos,buy,groupsFit,metadata,lanesFit,(lowCountsOf% e),e,perm,tag,j,side,t,a,onDate]

open LinearAlgebra.SpectralBooks ChordGraph Tagged.PassiveWindow
local notation "K" => siteLast h d k+1
local notation "D" => v.widePacketDegree


run_cmd Lean.modifyEnv fun env => ["wide_selected_signed_low", "wide_selected_signed_output", "wide_selected_signed_pair", "wide_selected_signed_compiled"].foldl (fun st head => Lean.LibrarySuggestions.nameDenyListExt.addEntry st head) env
open Lean Elab Term in
local elab "inferSelectedSignedLow% " body:term : term => elabTerm body none

-- The funded date uses the encoded native continuation. Transport only its
-- elected row set when the physical printing was recorded under the source code.
private theorem lowPrintAtFundedCode {Tape : Type} {W : Nat}
    (shape : WideCPU.Shape) (sites start : Nat) (fields : WideCPU.Fields shape)
    (input output : Memory W) (rows : Tape → Finset (Fin shape.candidates))
    (funded savedCode : Tape) (dateEq : funded = savedCode)
    (stamped : WideCPU.printedSiteRows shape sites start fields (rows savedCode) input output) :
    WideCPU.printedSiteRows shape sites start fields (rows funded) input output :=
  dateEq.symm ▸ stamped

open Lean Elab Term Meta in
local elab "lowSourceRows " receipt:term : term => do
  let mut head ← elabTerm receipt none
  for _ in [:8] do head := Lean.Expr.proj ``And 1 head
  return Lean.Expr.proj ``And 0 head

open Lean Elab Term Meta in
local elab "lowWithPurchasedPrint " native:term " withFacts " numeric:term " observed " evidence:term : term => do
  let produce ← elabTerm native none
  let package ← elabTerm numeric none
  let physicalPrint ← elabTerm evidence none
  let printedType ← inferType physicalPrint
  let some observedShape ← whnfUntil printedType ``WideCPU.printedSiteRows
    | throwError "expected physical selected packet rows in the retained heap"
  let outHeap := observedShape.getAppArgs.back!
  let producerAt := mkApp produce outHeap
  let pending ← whnf (← inferType producerAt)
  unless pending.isForall do throwError "the native packet output requires the physical print"
  let requiredPrinted := pending.bindingDomain!
  let some printedShape ← whnfUntil requiredPrinted ``WideCPU.printedSiteRows
    | throwError "the paid table must consume its own physical printing"
  let equalCodes := Lean.Expr.proj ``And 0 package
  let codeType ← whnf (← inferType equalCodes)
  unless codeType.isAppOfArity ``Eq 3 do throwError "expected equality of native and installed dated codes"
  let codes := codeType.getAppArgs
  let recordedSetPosition := printedShape.getAppNumArgs - 3
  let measuredSet := printedShape.getAppArgs[recordedSetPosition]!
  let argBack (e : Lean.Expr) (n : Nat) := e.getAppArgs[e.getAppNumArgs - n]!
  let putBack (e : Lean.Expr) (n : Nat) (x : Lean.Expr) := mkAppN e.getAppFn (e.getAppArgs.set! (e.getAppNumArgs - n) x)
  let expose (term : Lean.Expr) (name : Lean.Name) : MetaM Lean.Expr := do
    if term.isAppOf name then return term
    let some exposedNode ← whnfUntil term name | throwError "unexpected live-row spine at {name}"
    return exposedNode
  let measuredSet ← expose measuredSet ``wideBallotRows
  let entry ← expose (argBack measuredSet 1) ``entryMemory
  let origin ← expose (argBack entry 2) ``wideOrigin
  let header ← expose (argBack origin 2) ``WordSlots.header
  let rows ← withLocalDeclD `ticket codes[0]! fun ticket => do
    let next := putBack measuredSet 1 (putBack entry 2 (putBack origin 2 (putBack header 2 ticket)))
    mkLambdaFVars #[ticket] next
  let p := printedShape.getAppArgs
  let transported := mkAppN (mkConst ``lowPrintAtFundedCode) #[codes[0]!,p[0]!,p[1]!,p[2]!,p[3]!,p[4]!,p[6]!,p[7]!,rows,codes[1]!,codes[2]!,equalCodes,physicalPrint]
  return mkApp producerAt transported


open Lean Elab Term Meta in
local elab "lowFromSelectedHeap " snapshotName:term " via " generic:term : term => do
  let data ← elabTerm snapshotName none
  let readProcedure ← elabTerm generic none
  let prior := Lean.Expr.proj ``And 1 (Lean.Expr.proj ``And 1 data)
  let archive := Lean.Expr.proj ``And 0 prior
  let rom := Lean.Expr.proj ``And 0 (Lean.Expr.proj ``And 1 prior)
  let archiveType ← whnf (← inferType archive)
  unless archiveType.isAppOf ``ProcessingArchive do throwError "expected a recorded processing archive"
  return mkAppN readProcedure #[archiveType.getAppArgs.back!, Lean.Expr.proj ``ProcessingArchive 0 archive, rom]


open private readsAtProcessing from OAI.Hierarchy.TaggedWideFundedSelectedPacket
section
variable (processing : Memory (Native.wordBits h d Native.copies))
    (snapshotCheckout : PrefixAgreement.Low top processing (checkedOut chart top
      (v.wideOrigin h width S ((window).header es record seed) perm)))
    (readROM : HistoryRoles.RoleROM.Mounted ((g).siteROM rootROM) (SiteDirectory.table h d k) processing)

private abbrev selectedLowFromSnapshot :=
  let facts := readsAtProcessing v m ell short u δ ξ unitCost x cpu rate support perm j t a onDate
    processing snapshotCheckout readROM
  let tagBounds := support.size.partyTags a
  let sector := v.wideSpillDates h width ell unitCost v.maxBits first
  let shelfStart := (g).ballotStart (sector.roleRoot rankEnd 2) t
  (reference).2.production_low_word date extent support.size.tenderAge support.size.widthFloor
    (ProtocolRAMPurchaseSampler.bits (v.widePacketShelf h)) ((g).siteROM rootROM) ((g).siteStride rootROM)
    ((g).roleStart S t.castSucc) (sector.dateRole rankEnd t 0) processing facts.2.1 readROM
    facts.2.2.1 facts.2.2.2.1 tagBounds.1 tagBounds.2 shelfStart


end

open Lean Elab Term Meta in
local elab "purchasedLowRow% " result:term " at " site:ident side:ident capacity:ident total:ident parts:ident row:ident : term => do
  let lowTable ← elabTerm result none
  let inputs ← #[site, side, capacity, total, parts, row].mapM fun arg => getFVarFromUserName arg.getId
  return mkAppN lowTable inputs

/-- The released and installed widths read from the actual selected ballot in
the later control processor. Vacant paid rows have zero demand on either side. -/
abbrev wide_selected_signed_low (s : Fin K) (b : Bool) {cap : ℕ} {whole : (portGraph K).Port s→ℕ}
    (parts : Parts ((portGraph K).Port s) (Fin D) cap whole) (q : Fin D) := inferSelectedSignedLow%
  let facts := issuedFacts
  let scene:=memo
  let paidLow := lowFromSelectedHeap scene via
    (selectedLowFromSnapshot v m ell short u δ ξ unitCost x cpu rate support perm j t a onDate)
  let purchased := lowWithPurchasedPrint paidLow withFacts facts observed (lowSourceRows scene)
  purchasedLowRow% purchased at s b cap whole parts q

/-- Every physical signed control observation comes from the same returned
heap as the selected ballot. The argument order after the two native
endpoints is the numeric bound order of `wide_signed_control_fields`. -/
abbrev wide_selected_signed_output (s : Fin K) (pass want offer : (portGraph K).Port s→ℕ)
    (l : Parts ((portGraph K).Port s) (Fin D) (v.wideNeighborCap width unitCost) fun p=>pass p+want p)
    (r : Parts ((portGraph K).Port s) (Fin D) (v.wideNeighborCap width unitCost) fun p=>pass p+offer p) := inferSelectedSignedLow%
  let read:=v.wide_selected_ballot_snapshots m ell short u δ ξ unitCost x cpu rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag j false t a onDate
  v.wide_signed_control_fields h width ell unitCost v.maxBits first rootROM S rankEnd t s _ _
    pass want offer l r (read.2.2.2.2.2.2.2.2.2 s)

/-- Fix the measured role pair and the five physical output coordinates on
the chosen chronological control snapshot. Both closures use the same heap. -/
abbrev wide_selected_signed_pair (s : Fin K) := inferSelectedSignedLow%
  let captured:=v.wide_selected_control_roles m ell short u δ ξ unitCost x cpu rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag j false t a onDate
  SiteControls.signed_measured_pair (captured.2.1 t.castSucc) (captured.2.2 0 t.succ) captured.1
    s (v.wideNeighborCap width unitCost)

abbrev wide_selected_signed_compiled (s : Fin K) (pass want offer : (portGraph K).Port s→ℕ)
    (l : Parts ((portGraph K).Port s) (Fin D) (v.wideNeighborCap width unitCost) fun p=>pass p+want p)
    (r : Parts ((portGraph K).Port s) (Fin D) (v.wideNeighborCap width unitCost) fun p=>pass p+offer p) := inferSelectedSignedLow%
  let read:=v.wide_selected_ballot_snapshots m ell short u δ ξ unitCost x cpu rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag j false t a onDate
  v.wide_signed_compiled_output h width ell unitCost v.maxBits first rootROM S rankEnd t s _ _
    pass want offer l r (read.2.2.2.2.2.2.2.2.2 s)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
