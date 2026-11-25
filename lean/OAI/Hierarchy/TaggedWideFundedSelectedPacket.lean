import OAI.Hierarchy.TaggedWideFundedBallotSnapshots
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
local notation "memo" => v.wide_selected_ballot_snapshots m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j side t a onDate

include cpu in
/-- The physical old-role sheets contain every original commodity and catalogue row. -/
theorem wide_selected_row_count :
    Fintype.card (Commodity (Fin (2^h)) (Stages h d) k)+(v.widePlacement h width).catalogue.rows
      ≤ 2^(Native.wordBits h d Native.copies) := by
  have packed:=v.wide_old_rows h width
  change (g).physical=_ at packed
  have consists : (g).physical ≤ (g).roleSpan := by
    dsimp only [WideCPU.Dated.roleSpan,HistoryRoles.DatedRoleSheets.span]
    omega
  have firstPage : 3*(g).roleSpan ≤ ((events v.mesh).length+1)*(3*(g).roleSpan) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have allocation : (g).physical ≤ (g).rolesEnd S := by
    change _ ≤ S+((events v.mesh).length+1)*(3*(g).roleSpan)
    omega
  have stop : (g).rolesEnd S ≤ (g).workEnd S := by
    dsimp only [WideCPU.Dated.workEnd,WideCPU.Dated.slotStart,WideCPU.Dated.maskStart,
      WideCPU.Dated.controlStart,WideCPU.endOf]; omega
  have after : (g).workEnd S+2 ≤ (lay).floor := v.wide_window_after_terminal x _
  have pruning : (lay).floor ≤ (lay).pruneScratch := Nat.le_add_right _ _
  have paid := (v.wide_full_end x m ell short u δ ξ unitCost cpu.room).trans cpu.room.upper
  rw [PurchaseInventory.card_commodity]
  omega

section
variable (processing : Memory (Native.wordBits h d Native.copies))
    (snapshotCheckout : PrefixAgreement.Low top processing (checkedOut chart top
      (v.wideOrigin h width S ((window).header es record seed) perm)))
    (readROM : HistoryRoles.RoleROM.Mounted ((g).siteROM rootROM) (SiteDirectory.table h d k) processing)

private abbrev readsAtProcessing :=
  let tall:=support.size.tenderAge
  have code : (date).code=record :=
    (v.wide_funded_date_code h width S extent perm seed cpu.age cpu.ready.credit cpu.ready.size_le
      (chosen).prior (chosen).choice (chosen).future).trans
      (congrArg (CalendarTape.encode sl es base) (WireTelescope.CalendarTape.Prefix.pathVisitAt_suffix j t onDate))
  have checkout : PrefixAgreement.Low top processing (checkedOut chart top
      (v.wideOrigin h width S ((window).header es (date).code seed) perm)) := by
    rw [code]
    exact snapshotCheckout
  have bound : (g).romEnd rootROM < 2^(Native.wordBits h d Native.copies) := by
    have gap:=(support.size.spill cpu.room).gap
    have registers:=cpu.scratch
    omega
  have area : rootROM+(g).sites+(g).siteDirectorySize ≤ (g).romEnd rootROM := by
    simp only [WideCPU.Dated.romEnd,WideCPU.Dated.maskROM,WideCPU.Dated.controlROMStart,
      WideCPU.Dated.firstROM,WideCPU.Dated.siteROM,WideCPU.endOf]
    omega
  have siteFit : SiteDirectory.size h d k ≤ 2^(Native.wordBits h d Native.copies) := by
    change (g).siteDirectorySize ≤ _
    omega
  have partyFit : siteLast h d k+1 ≤ 2^(Native.wordBits h d Native.copies) := by
    change (g).sites ≤ _
    omega
  let reads := (reference).2.packet_reads_on date extent tall support.size.widthFloor
    ((g).siteROM rootROM) processing checkout readROM siteFit partyFit
  let tokens:=support.size.partyTags a
  let tags:=(reference).2.packet_tag_on date extent tall support.size.widthFloor
    ((g).siteROM rootROM) processing checkout readROM siteFit tokens.1 tokens.2
  And.intro code (And.intro (show PrefixAgreement.Low top _ _ from checkout)
    (And.intro siteFit (And.intro partyFit (And.intro reads tags))))


private abbrev tableAtProcessing :=
  let facts := v.readsAtProcessing m ell short u δ ξ unitCost x cpu rate support perm j t a onDate
    processing snapshotCheckout readROM
  let tagBounds := support.size.partyTags a
  let sector := v.wideSpillDates h width ell unitCost v.maxBits first
  let shelfStart := (g).ballotStart (sector.roleRoot rankEnd 2) t
  (reference).2.production_word date extent support.size.tenderAge support.size.widthFloor
    (ProtocolRAMPurchaseSampler.bits (v.widePacketShelf h)) ((g).siteROM rootROM) ((g).siteStride rootROM)
    ((g).roleStart S t.castSucc) (sector.dateRole rankEnd t 0) processing facts.2.1 readROM
    facts.2.2.1 facts.2.2.2.1 tagBounds.1 tagBounds.2 shelfStart

end

open Lean Elab Term Meta in
local elab "readsFromSelectedHeap " snapshotName:term " via " generic:term : term => do
  let data ← elabTerm snapshotName none
  let readProcedure ← elabTerm generic none
  let prior := Lean.Expr.proj ``And 1 (Lean.Expr.proj ``And 1 data)
  let archive := Lean.Expr.proj ``And 0 prior
  let rom := Lean.Expr.proj ``And 0 (Lean.Expr.proj ``And 1 prior)
  let archiveType ← whnf (← inferType archive)
  unless archiveType.isAppOf ``ProcessingArchive do throwError "expected a recorded processing archive"
  return mkAppN readProcedure #[archiveType.getAppArgs.back!, Lean.Expr.proj ``ProcessingArchive 0 archive, rom]

open Lean Elab Term Meta in
local elab "fundedBallotAt " head:ident "[" operands:term,* "]" : term => do
  let args ← operands.getElems.mapM (fun operand => elabTerm operand none)
  let c ← resolveGlobalConstNoOverload head
  return mkAppN (← mkConstWithFreshMVarLevels c) args

open Lean Elab Command Term Meta in
local elab "recordSelectedPacketResult " publicId:ident " from " body:term : command => do
  let nm := (← getCurrNamespace) ++ publicId.getId
  runTermElabM fun context => do
    let answer ← withoutErrToSorry <| elabTerm body none
    synthesizeSyntheticMVarsNoPostponing
    let complete ← mkLambdaFVars context (← instantiateMVars answer) (usedOnly := true)
    let value ← Term.levelMVarToParam complete
    let type ← instantiateMVars (← inferType value)
    if value.hasFVar || value.hasMVar || value.hasSorry || type.hasFVar || type.hasMVar || type.hasSorry then
      throwError "the original selected packet-read operands must be fully determined"
    addDecl (.defnDecl {
      name := nm
      levelParams := (collectLevelParams {} type).params.toList
      type := type
      value := value
      hints := .regular 1
      safety := .safe })

-- The funded date uses the encoded native continuation. Transport only its
-- elected row set when the physical printing was recorded under the source code.
private theorem printedRowsAtFundedDate {Tape : Type} {W : Nat}
    (shape : WideCPU.Shape) (sites start : Nat) (fields : WideCPU.Fields shape)
    (input output : Memory W) (rows : Tape → Finset (Fin shape.candidates))
    (funded savedCode : Tape) (dateEq : funded = savedCode)
    (stamped : WideCPU.printedSiteRows shape sites start fields (rows savedCode) input output) :
    WideCPU.printedSiteRows shape sites start fields (rows funded) input output :=
  dateEq.symm ▸ stamped

open Lean Elab Term Meta in
local elab "beforePacketPrint " receipt:term : term => do
  let mut head ← elabTerm receipt none
  for _ in [:8] do head := Lean.Expr.proj ``And 1 head
  return Lean.Expr.proj ``And 0 head

open Lean Elab Term Meta in
local elab "tableForPrintedHeap " native:term " withFacts " numeric:term " observed " evidence:term : term => do
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
  let transported := mkAppN (mkConst ``printedRowsAtFundedDate) #[codes[0]!,p[0]!,p[1]!,p[2]!,p[3]!,p[4]!,p[6]!,p[7]!,rows,codes[1]!,codes[2]!,equalCodes,physicalPrint]
  return mkApp producerAt transported

local notation "packetSnapshot" => fundedBallotAt wide_selected_ballot_snapshots [F,(inferInstance : Field F),k,p,q,Q,σ,Λ,κ,A,v,m,ell,short,u,δ,ξ,unitCost,N,x,cpu,rate,support,
    prices,C,pricePos,buy,groupsFit,metadata,lanesFit,b,e,perm,tag,j,side,t,a,onDate]
local notation "returnedPacket" => fundedBallotAt wide_selected_returned_ballot [F,(inferInstance : Field F),k,p,q,Q,σ,Λ,κ,A,v,m,ell,short,u,δ,ξ,unitCost,N,x,cpu,rate,support,
    prices,C,pricePos,buy,groupsFit,metadata,lanesFit,b,e,perm,tag,j,side,t,a,onDate]
local notation "nativeReads" => readsFromSelectedHeap packetSnapshot via
  (v.readsAtProcessing m ell short u δ ξ unitCost x cpu rate support perm j t a onDate)
local notation "nativeTable" => readsFromSelectedHeap packetSnapshot via
  (v.tableAtProcessing m ell short u δ ξ unitCost x cpu rate support perm j t a onDate)

-- The original reference tender at the actual ballot-processing step.
recordSelectedPacketResult wide_selected_packet_reads from (nativeReads)

-- The extended packet word at each original site and each column.
recordSelectedPacketResult wide_selected_packet_table from (
  tableForPrintedHeap nativeTable withFacts nativeReads observed (beforePacketPrint packetSnapshot))

-- The same paid packet columns on the genuine returned memory.
recordSelectedPacketResult wide_selected_returned_packet_table from (
  tableForPrintedHeap nativeTable withFacts nativeReads observed returnedPacket)

run_cmd Lean.modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_packet_reads"
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_packet_table"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_returned_packet_table"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
