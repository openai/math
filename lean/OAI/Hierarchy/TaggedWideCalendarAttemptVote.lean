import OAI.Hierarchy.TaggedWideCalendarAttemptAt
import OAI.Hierarchy.TaggedWideSelectedSignedWidths
import OAI.Hierarchy.TaggedWideSelectedSignedBounds
import OAI.Hierarchy.TaggedWideSelectedSignedEntry
import OAI.Hierarchy.TaggedWideSelectedSignedFields
import OAI.Hierarchy.TaggedWideSelectedSignedBits

namespace OAI
/-! # Measuring the real signed row on its two funded chronological apertures -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option cleanup.letToHave false
set_option maxRecDepth 12288
set_option maxHeartbeats 2200000
open private preclipSiteFormula selectedPreclipSiteOnNamedLayout from OAI.Hierarchy.TaggedWideCalendarAttemptAt

/-- Restrict a paid layout to one site before specializing the dated widths. -/
private def paidReadSiteChart {siteCount laneCount : Nat} {bitAt : Fin siteCount → Type}
    {paidLayout : Sigma bitAt ↪ Fin siteCount × Fin laneCount}
    (paidSite : preclipSiteFormula (Fin siteCount) bitAt (Fin laneCount) paidLayout)
    (siteId : Fin siteCount) : bitAt siteId ↪ Fin laneCount :=
  LedgerStep.siteChart paidLayout paidSite siteId

open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.BranchRoles Tagged.WideCalendarSites
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged.WideStack.Leaf ProtocolRAMReportedPorts
open private selectedPlacementBodyEq from OAI.Hierarchy.TaggedWideCalendarAttemptAt

-- Keep the raw indexed proof and the captured named site law as independent
-- arguments. Only the physical embeddings determine the middle gate.
private theorem fundedReadOnPaidMiddle {K N : ℕ} {B : Widths K}
    (indexed selected : (Σ s, SiteBit B s) ↪ Fin K × Fin N)
    (indexedSite : ∀ s (u : SiteBit B s), (indexed ⟨s,u⟩).1 = s)
    (paidSite : preclipSiteFormula (Fin K) (SiteBit B) (Fin N) selected)
    (s : Fin K) (z : State B s) (alignment : indexed = selected)
    (P : (Fin N → Bool) → Prop)
    (read : P (LedgerStep.middle s (LedgerStep.siteChart indexed indexedSite s) z)) :
    P (LedgerStep.middle s (paidReadSiteChart paidSite s) z) := by
  have columns (u : SiteBit B s) : (indexed ⟨s,u⟩).2 = (selected ⟨s,u⟩).2 :=
    congrArg (fun (layout : (Σ s, SiteBit B s) ↪ Fin K × Fin N) => (layout ⟨s,u⟩).2) alignment
  have sameChart : LedgerStep.siteChart indexed indexedSite s = paidReadSiteChart paidSite s :=
    Function.Embedding.ext columns
  exact (congrArg (fun chart => P (LedgerStep.middle s chart z)) sameChart).mp read

open Lean Elab Term Meta in
private partial def voteGateMiddle (term : Lean.Expr) (replaceWith : Option Lean.Expr) :
    Option Lean.Expr := Id.run do
  if term.isAppOfArity ``LedgerStep.middle 6 then return some (replaceWith.getD term)
  unless term.isAppOfArity ``Sum.elim 5 do return none
  let args := term.getAppArgs
  for i in #[3,4] do
    if let some child := voteGateMiddle args[i]! replaceWith then
      return some (if replaceWith.isSome then mkAppN term.getAppFn (args.set! i child) else child)
  return none

open Lean Elab Term Meta in
private def movePaidReading (observed next : Lean.Expr) : TermElabM Lean.Expr := do
  let sourceTy := (← inferType observed).consumeMData
  let .letE p pt pv state pb := sourceTy | throwError "expected the signed partition"
  let .letE y yt yv gate yb := state | throwError "expected the transported paid state"
  let .letE g gt gv rows gb := gate | throwError "expected the signed gate"
  let some old := voteGateMiddle gv none | throwError "expected the funded site gate"
  unless next.isAppOfArity ``LedgerStep.middle 6 do throwError "expected the named site middle"
  let #[siteCount0,laneCount0,earnedWidths0,partySite0,oldChart,state0] := old.getAppArgs | throwError "expected the dated state"
  let newChart := next.getAppArgs[4]!
  unless oldChart.isAppOfArity ``LedgerStep.siteChart 6 && newChart.isAppOfArity ``paidReadSiteChart 6 do
    throwError "expected the original site chart and its paid counterpart"
  let oldArgs := oldChart.getAppArgs
  let nextArgs := newChart.getAppArgs
  let namedLayout := nextArgs[3]!
  unless namedLayout.isAppOf ``selected_preclip_layout do throwError "expected the selected original placement"
  -- The selected embedding is the dependent application of the very same funded lower producer.
  let mut alignment ← mkConstWithFreshMVarLevels ``selectedPlacementBodyEq
  for arg in namedLayout.getAppArgs do
    alignment ← mkCongrFun alignment arg
  withLocalDeclD `gateMiddle (← inferType old) fun middleValue => do
    let some updated := voteGateMiddle gv (some middleValue) | throwError "expected the funded gate aperture"
    let prop := Expr.letE p pt pv (.letE y yt yv (.letE g gt updated rows gb) yb) pb
    let predicate ← mkLambdaFVars #[middleValue] prop
    return mkAppN (mkConst ``fundedReadOnPaidMiddle) #[siteCount0,laneCount0,earnedWidths0,oldArgs[3]!,namedLayout,
      oldArgs[4]!,nextArgs[4]!,partySite0,state0,alignment,predicate,observed]


open Lean Elab Term Meta in
local elab "trueFundedTargetBits%" : term => do
  let target ← mkConstWithFreshMVarLevels ``selected_signed_target_bits
  forallBoundedTelescope (← inferType target) (some 43) fun args _ => do
    unless args.size == 43 do throwError "expected the full selected bit signature"
    let observed := mkAppN target args
    let .letE _ _ _ (.letE _ _ _ (.letE _ _ gate _ _) _) _ := (← inferType observed).consumeMData
      | throwError "expected the archived assignment, state, and gate"
    let some old := voteGateMiddle gate none | throwError "expected the selected site middle"
    let rawChart := old.getAppArgs[4]!
    let stateType := (← inferType args[42]!).consumeMData
    let namedLayout := (stateType.getAppArgs[1]!).appArg!
    unless namedLayout.isAppOfArity ``selected_preclip_layout 40 do throwError "expected the selected placement in the original state"
    let siteLaw := mkAppN (← mkConstWithFreshMVarLevels ``selectedPreclipSiteOnNamedLayout) namedLayout.getAppArgs
    let paidChart := mkAppN (← mkConstWithFreshMVarLevels ``paidReadSiteChart) ((rawChart.getAppArgs.set! 3 namedLayout).set! 4 siteLaw)
    let paidMiddle := mkAppN old.getAppFn (old.getAppArgs.set! 4 paidChart)
    let result ← movePaidReading observed paidMiddle
    mkLambdaFVars args result

private theorem actualFundedTargetBitRead : type_of% trueFundedTargetBits% :=
  no_implicit_lambda% trueFundedTargetBits%

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun entries => "actualFundedTargetBitRead" :: entries

open Lean Elab Term Meta in
local elab "paidReadSiteChart% " paidTerm:term " atSite " siteExpr:term : term => do
  let paid ← withSynthesize (postpone := .no) <| elabTerm paidTerm none
  let some paidType ← whnfUntil (← inferType paid) ``preclipSiteFormula
    | throwErrorAt paidTerm "expected a site law for the paid layout"
  let #[physicalSites, bitAt, physicalLanes, paidLayout] := paidType.getAppArgs
    | throwErrorAt paidTerm "expected a site family and lane family"
  let some siteFin ← whnfUntil physicalSites ``Fin | throwError "expected the finite physical site count"
  let some laneFin ← whnfUntil physicalLanes ``Fin | throwError "expected the finite physical lane count"
  return mkAppN (← mkConstWithFreshMVarLevels ``paidReadSiteChart)
    #[siteFin.appArg!, laneFin.appArg!, bitAt, paidLayout, paid, ← elabTerm siteExpr none]

open Lean Elab Term Meta in
local elab "applyCalendarLayoutOperand% " producer:ident "[" values:term,* "]" : term => do
  let format ← getFVarFromUserName `v
  let some formatType ← whnfUntil (← inferType format) ``FixedProtocolFormat
    | throwError "expected the dated protocol format"
  let name ← resolveGlobalConstNoOverload producer
  let mut fn := mkAppN (← mkConstWithFreshMVarLevels name) formatType.getAppArgs
  for value in values.getElems do fn := mkApp fn (← elabTerm value none)
  return fn

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unit
local notation "S" => v.wideInstalledSize x m ell unit g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unit g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unit g
    (v.wide_dated_sites h width ell unit) (v.wide_dated_edges h width ell unit) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "D" => v.parentShared x m ell short unit ((es).length+1)
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
local notation "base" => v.wideOrigin h width S seed

variable (routeAge : v.routingHeight≤x.h)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "Z" => v.routedSchedule h width S arenaRoom seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit routeAge support.size.widthFloor support.size.words
local notation "rout" => (Z).nativeRouting D
local notation "sites" => SignedSites.ofCalendar (cpu:=cpu) Z control v.calendarTerminalWidth
  (v.calendarTerminalPins x m ell short)
local notation "source" => fun _ : Fin (m+1)=>slots
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates h v.W k v.wideJobs slots ((menu).height i x) (count i)
local notation "Buy" => PurchaseList (F:=F) (C:=C) menu x source target count
local notation "Ex" => OpenPins h width (rout).catalyst
local notation "report" π:arg j:arg => v.wide_reported_path h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words j
variable (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
variable (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
local notation "path" => (Fintype.equivFin (Path sl es (base perm))).symm i
local notation "record" => CalendarTape.encode sl es (base perm) path

open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.BranchRoles Tagged.WideCalendarSites
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged.WideStack.Leaf ProtocolRAMReportedPorts
variable (height : v.BranchRoleHeight h width)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unit cpu.room).2
local notation "W" => Native.wordBits h d Native.copies
local notation "root" => (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix sl es (base perm) es (base perm))
local notation "tree" => WireTelescope.CalendarTape.Prefix.cursorSlot («slot»:=sl) (events:=es) (x₀:=base perm)
local notation "ws" => WireTelescope.CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "top" => WireTelescope.CalendarTape.Prefix.atCursor root
local notation "branch" => WireTelescope.CalendarTape.Prefix.histories root path
local notation "stop" => terminal tree es top branch
local notation "input" => (reader).format.windows.header es record seed
local notation "bill" => v.wide_reported_path_native h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words path
local notation "admitted" => (bill).choose
local notation "cost" => (bill).choose_spec.choose
local notation "names" => (bill).choose_spec.choose_spec.choose
local notation "accepted" => (bill).choose_spec.choose_spec.choose_spec.1
local notation "native" => v.wide_native_report h width S perm.symm input v.maxBits Sfit admitted
  cpu.ready.credit cpu.ready.size_le cost (0:Word W) names
local notation "runAt" => v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "out" => (runAt).2.2.2.choose
local notation "actual" => Classical.choice (support.funding S Sfit perm.symm input admitted cpu.ready.credit
  cpu.ready.size_le cost (0:Word W) names accepted)
local notation "install" ok:arg => FundedCutRows.rowData v x S perm.symm input m ell short unit (native).rows
  (native).geometry actual prices pricePos buy groupsFit metadata ok lanesFit
local notation "geom" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "ports" => WideMemory.H h v.W k v.wideJobs
local notation "b" => (v.widePlacement h width).catalogue
local notation "order" => v.wideOrder h width
local notation "roles" => HistoryRoles.ceiling v.sampler («h»:=h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unit v.keepLimit (fuel v.mesh) width
local notation "view" => v.wideHistoryUnit unit*width
local notation "times" => ((es).length+1)*Fintype.card ((r:Public v.sampler h v.W k v.wideJobs)×Fin (roles r))
local notation "shape" => v.widePathRoles h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "pins" => v.widePathCells h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "place" => timelineFin tree ws pins es top branch
local notation "replayed" => cursorReport perm ((Z).width perm) ((Z).reported perm) branch
local notation "Rpt" => CoreBoard.Report perm d k width (fuel v.mesh*width) v.radius 1 (ws stop)
local notation "table" r:arg => (⟨(r).edges,(r).rows⟩ : CalendarTerms.RowBoard)
local notation "plan" r:arg => CalendarTerms.RankedRows (F:=F) (geom).index D (dir).groups ports (2^ell) width m times view (table r)

local notation "same" => v.wide_selected_geometry m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "sameRows" => congrArg (fun r:RowGeometry h d k width (fuel v.mesh*width) v.radius 1=>
  (⟨r.1,r.2.1⟩:CalendarTerms.RowBoard)) same
local notation "kept" => (native).geometry.links.Keep (2^h)
local notation "recorded" => v.wideCalendarPartyPlace m ell short u δ ξ x cpu Z perm i height (fun _=>rfl)
local notation "rnk" ok:arg => CalendarTerms.RankedRows.onBranch Z perm i sameRows (install ok)
local notation "wordTable" => (r : Fin (replayed).edges)→Fin (2^((replayed).rows r).width)
local notation "states" => SiteChoices tree ws es top branch

local notation "data" ok:arg words:arg q:arg => v.calendarDayPins (C:=C) m ell short u δ ξ x cpu support routeAge
  prices pricePos groupsFit metadata lanesFit buy e perm i tag height ok words q
local notation "scr" => v.wideInstalledLayout x m ell short u δ ξ unit g
local notation "first" => (scr).pruneScratch+(scr).pruneRows+1
local notation "rom" => v.wideInstalledRoot x
local notation "time" => SignedSites.calendarTime (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unit)
local notation "actualRow" s:arg j:arg => v.calendarRow h width ell unit v.maxBits rom S ((g).romEnd rom) ((g).workEnd S)
  first G time s j (control.spillRead s j) (control.signedRead s j) (control.mode s j) control.tag control.lane
local notation "step" => WireTelescope.CalendarTape.Prefix.atStep ((Z).width perm) ((Z).operator perm)
local notation "matrixAt" j:arg => indexedStep tree ws step es top branch j
local notation "valAt" q:arg s:arg j:arg => datedState tree ws s es top branch j (q s)


-- Use the stored physical operand type from the selected calendar day's own interface.
open Lean Elab Term in
local elab "calendarFundedOperand% " selected:str : term => do
  let original ← getConstInfo ``calendarDayPins
  let selection := Name.mkSimple selected.getString
  let format := (← Meta.inferType (← Meta.getFVarFromUserName `v)).getAppArgs
  let field := format[1]!
  let ambientRatio := format[4]!
  let mut current := original.type
  let mut supplied : Array Lean.Expr := #[]
  for _ in [:100] do
    match current with
    | .forallE binder domain rest info =>
      if binder == selection then return domain.instantiateRev supplied
      let argument ← if info == .instImplicit then pure field else if binder == `q then pure ambientRatio else Meta.getFVarFromUserName binder
      supplied := supplied.push argument
      current := rest
    | _ => break
  throwError "the original funded day has no physical operand {selection}"

variable (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (ok : calendarFundedOperand% "ok") (words : calendarFundedOperand% "words")
    (q : calendarFundedOperand% "statesAt") (site : Fin (siteLast h d k+1))
local notation "voteAt" => v.wide_routed_attempt_on_visit h width S arenaRoom perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le Sfit routeAge support.size.widthFloor support.size.words path date day
local notation "x₀" => valAt q site date.castSucc
local notation "y₀" => valAt q site date.succ

local notation "siteLaw" => applyCalendarLayoutOperand% selectedPreclipSiteOnNamedLayout [κ, A, v, m, ell, short, u, δ, ξ, unit, N, x, cpu, v.calendarUnit_rate, support, prices, C, pricePos, buy, groupsFit, metadata, lanesFit, (rout).catalyst, e, perm, tag, path, routeAge, height, date, a, day]
open LinearAlgebra.SpectralBooks.SiteTensor
open WideCPU WideControlJoin
local notation "visit" => Prefix.pathVisitAt path date day
local notation "stamp" => (es).length-(Event.attempt a::(visit).tail).length
local notation "whereAt" => siteNumber h d k
local notation "nativeSlots" => v.nativeSlots (v.widePlacement h width) h width a
local notation "cut" c:arg => v.wide_funded_date h width S arenaRoom perm seed cpu.age cpu.ready.credit
    cpu.ready.size_le (visit).prior c
local notation "ref" => v.wide_reference_date h width S arenaRoom perm seed cpu.age cpu.ready.credit
    cpu.ready.size_le (visit).prior
local notation "oldMount" => (b).coreMount perm.symm whereAt order (visit).mem
local notation "spent" => v.wirePaidAt h width v.maxBits stamp (visit).mem
local notation "avail" => fun ledgerGood=>v.wireGoodsAt h width stamp (visit).mem ((nativeSlots).symm ledgerGood)
local notation "reserve" c:arg => fun axis=>(fuel v.mesh*width-v.wireUsedAt h width stamp (visit).mem axis)-
    (cut c).reserveDebit axis
local notation "rest" => (oldMount).actual.chordWidths spent +
    (CoreBoard.ordinalGoods perm.symm whereAt nativeSlots).chordWidths (fun ledgerGood=>(avail) ledgerGood-(cut (ref).1).debit ledgerGood) +
    (catalystGraph whereAt).chordWidths (reserve (ref).1)
local notation "pos" => (visit).choice
local notation "slotsUsed" => fun l=>((ref).2.row arenaRoom support.size.tenderAge support.size.widthFloor l).input
local notation "offered" => fun l=>((ref).2.tender arenaRoom support.size.tenderAge support.size.widthFloor l).post (pos l)
local notation "U" => rest+∑l,slotsUsed l
local notation "V" => rest+∑l,offered l
local notation "carry" => (oldMount).actual.chordWidths spent+(cut pos).afterMount.actual.chordWidths (cut pos).paid+
    (catalystGraph whereAt).chordWidths (reserve pos)
local notation "transfer" => FeedTransfer.afterVote nativeSlots (fun c=>(cut c).afterGoods) (fun c=>(cut c).spill) pos
local notation "middleWidth" => FeedTransfer.input (π:=perm.symm) («place»:=whereAt) carry transfer
local notation "beforeWidth" => ws (boundaryState tree es top branch date.castSucc)
local notation "inputShape" => v.selected_signed_input_width m ell short u δ ξ unit x cpu perm path height date a day routeAge
local notation "offerShape" => v.selected_signed_offer_width m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path height date a day routeAge
local notation "left" => v.selectedSignedInputParts m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path height date a day site U inputShape
local notation "right" => v.selectedSignedOfferParts m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path height date a day site V offerShape
local notation "funds" => v.selected_signed_bounds m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path height date a day site U V inputShape offerShape
local notation "sockets" => shelfSlot («h»:=h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "read" => LedgerStep.substepWord (cap:=v.wideNeighborCap width unit) G es roles sockets time date site false
local notation "inner" z:arg => LedgerStep.middle site (paidReadSiteChart% (siteLaw) atSite site) z

-- The selected bound receipt contains the four physical inequalities used by the signed row.
open Lean Elab Term in
local elab "applyPaidVoteBounds% " rowFunction:term " withBounds " receiptTerm:term : term => do
  let row ← withSynthesize (postpone := .no) <| elabTerm rowFunction none
  let paid ← withSynthesize (postpone := .no) <| elabTerm receiptTerm none
  let later := Lean.Expr.proj ``And 1 paid
  let rooms := Lean.Expr.proj ``And 1 later
  return mkAppN row #[.proj ``And 0 paid, .proj ``And 0 later,
    .proj ``And 0 rooms, .proj ``And 1 rooms]

/-- Evaluate the selected signed row on the measured input and preclip charts.
The native read obligations concern just the returned controls, both sets of
carried bits and the two published neighbor indices. -/
abbrev calendarAttemptVoteMeasure (word : v.PartyWordBounds h width unit)
    (entry : U=beforeWidth) (join : V=middleWidth) (z : State middleWidth site) :=
  applyPaidVoteBounds% (v.selected_signed_entry (Sel:=Fin (CalendarTape.bits sl es))
    (Data:=D ⊕ Fin (HistoryRoles.stride k v.sampler.degree v.wideJobs * v.wideNeighborCap width unit))
    m ell short u δ ξ unit x cpu v.calendarUnit_rate support prices pricePos buy groupsFit
    metadata lanesFit e perm tag path date a day control word site read record
      (Sum.elim (data ok words q) (inner z)) rest (cast (congrArg (fun T=>State T site) entry.symm) x₀)
      (cast (congrArg (fun T=>State T site) join.symm) z) left right) withBounds (funds)

-- Install the original signed controls and neighbor reads. The remaining two
-- arguments are the original carried bits, in source and target order.
open Lean Elab Term in
local elab "applyPaidVoteColumns% " rowTerm:term " withColumns " fieldsTerm:term : term => do
  let row ← withSynthesize (postpone := .no) <| elabTerm rowTerm none
  let columns ← withSynthesize (postpone := .no) <| elabTerm fieldsTerm none
  let rowWithControl := mkApp row (.proj ``And 0 columns)
  let neighbors := Lean.Expr.proj ``And 1 columns
  Meta.forallBoundedTelescope (← Meta.inferType rowWithControl) (some 2) fun readings _ => do
    unless readings.size == 2 do
      throwErrorAt rowTerm "expected the two carried-bit readings of the signed row"
    let measured := mkAppN rowWithControl (readings ++ #[.proj ``And 0 neighbors, .proj ``And 1 neighbors])
    Meta.mkLambdaFVars readings measured

local notation "fundedVoteDataProof" =>
  applyPaidVoteColumns% (v.calendarAttemptVoteMeasure (C:=C) m ell short u δ ξ x cpu control support routeAge
    prices pricePos groupsFit metadata lanesFit buy e perm i tag height date a day ok words q site
    word entry join z) withColumns (v.selected_signed_fields m ell short u δ ξ unit x cpu v.calendarUnit_rate
    support prices pricePos buy groupsFit metadata lanesFit e perm tag path date a day height routeAge word site)

/-- The registered counter and neighbor columns of the selected participant
discharge the control reads for both apertures of the signed row. -/
theorem calendarAttemptVoteData
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤x.h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (ok : calendarFundedOperand% "ok") (words : calendarFundedOperand% "words")
    (q : calendarFundedOperand% "statesAt") (site : Fin (siteLast h d k+1))
    (word : v.PartyWordBounds h width unit)
    (entry : U=beforeWidth) (join : V=middleWidth) (z : State middleWidth site) :
    type_of% fundedVoteDataProof :=
  no_implicit_lambda% fundedVoteDataProof

open Lean Elab Term in
local elab "readPaidVoteBits% " row:term " fromReads " sourceRead:term "," targetRead:term : term => do
  let measured ← withSynthesize (postpone := .no) <| elabTerm row none
  let firstRead ← withSynthesize (postpone := .no) <| elabTerm sourceRead none
  let secondRead ← withSynthesize (postpone := .no) <| elabTerm targetRead none
  return mkAppN measured #[firstRead, secondRead]

local notation "fundedVoteProof" =>
  readPaidVoteBits% (v.calendarAttemptVoteData (C:=C) m ell short u δ ξ x cpu control support routeAge prices pricePos
    groupsFit metadata lanesFit buy e perm i tag height date a day ok words q site word entry join z) fromReads
    (v.selected_signed_source_bits (C:=C) m ell short u δ ξ x cpu support routeAge prices pricePos
      groupsFit metadata lanesFit buy e perm i tag height ok words q date site a day entry (inner z)),
    (v.actualFundedTargetBitRead (C:=C) m ell short u δ ξ x cpu support routeAge prices pricePos
      groupsFit metadata lanesFit buy e perm i tag height ok words q date site a day join z)

/-- The value of the allocated physical signed half on the true selected
calendar date, for every central state of the subsequent contraction. -/
theorem calendar_attempt_vote
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤x.h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (ok : calendarFundedOperand% "ok") (words : calendarFundedOperand% "words")
    (q : calendarFundedOperand% "statesAt") (site : Fin (siteLast h d k+1))
    (word : v.PartyWordBounds h width unit)
    (entry : U=beforeWidth) (join : V=middleWidth) (z : State middleWidth site) :
    type_of% fundedVoteProof :=
  no_implicit_lambda% fundedVoteProof

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun entries => "calendarAttemptVoteMeasure" :: entries
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun entries => "calendarAttemptVoteData" :: entries
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun entries => "calendar_attempt_vote" :: entries

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
