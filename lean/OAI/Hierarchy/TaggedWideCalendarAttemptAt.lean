import OAI.Hierarchy.TaggedWideCalendarDayPins
import OAI.Hierarchy.TaggedWideCalendarControlRoom
import OAI.Hierarchy.TaggedWideSelectedPreclipLayout
import OAI.Hierarchy.TaggedWideFundedIndexedReplay

namespace OAI
/-! # The measured local contraction at an individual attempted native date -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12288
set_option maxHeartbeats 2200000
set_option cleanup.letToHave false
open ProbeStage CoreBoard CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.ChordGraph
open WireTelescope.PassMatrix
open scoped Fin.CommRing

/- Express the site law using the indexed placement itself, before the selected
processor and its two concrete funded dates are substituted. -/
private def preclipSiteFormula (S : Type) (bits : S → Type) (L : Type)
    (placement : Sigma bits ↪ (S × L)) : Prop :=
  ∀ (siteId : S) (z : bits siteId), (placement ⟨siteId, z⟩).1 = siteId

open Lean Elab Term Meta in
local elab "namedPreclipSiteType% " producer:ident : term => do
  let original ← getConstInfo (← resolveGlobalConstNoOverload producer)
  let formula ← getConstInfo ``preclipSiteFormula
  forallTelescope original.type fun args result => do
    let some embedding ← whnfUntil result ``Function.Embedding
      | throwError "expected the selected preclip embedding"
    let #[domain, target] := embedding.getAppArgs
      | throwError "expected the embedding domain and target"
    let some sigma ← whnfUntil domain ``Sigma
      | throwError "expected an intermediate bit at a dependent site"
    let some product ← whnfUntil target ``Prod
      | throwError "expected a physical site and lane"
    let #[sites, bits] := sigma.getAppArgs | throwError "expected the preclip site family"
    let #[_, lanes] := product.getAppArgs | throwError "expected the preclip lane type"
    let placement := mkAppN (← mkConstWithFreshMVarLevels original.name) args
    let law := mkAppN (← mkConstWithFreshMVarLevels formula.name) #[sites,bits,lanes,placement]
    mkForallFVars args law

private theorem fundedSiteOfIndexedLayout : namedPreclipSiteType% FundedDate.preclip_indexed_layout :=
  @FundedDate.preclip_indexed_site

/- The indexed site theorem uses the very same funded operands as the
selected layout. Extract them from that layout once at its generic type. -/
open Lean Elab Term Meta in
local elab "namedPreclipFundedSiteValue%" : term => do
  let placement ← getConstInfo ``Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.selected_preclip_layout
  let indexed ← getConstInfo ``Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.FundedDate.preclip_indexed_layout
  let site ← getConstInfo ``fundedSiteOfIndexedLayout
  forallTelescope placement.type fun args _ => do
    let body := (placement.value!.beta args).consumeMData
    unless body.isAppOf indexed.name do
      throwError "the selected placement must use its original funded indexed layout"
    let operands := body.getAppArgs
    let mut kind := indexed.type
    let mut arity := 0
    while let .forallE _ _ next _ := kind do
      arity := arity + 1
      kind := next
    unless arity == operands.size do
      throwError "expected all {arity} operands of the funded placement"
    let proof := mkAppN (mkConst site.name body.getAppFn.constLevels!) operands
    mkLambdaFVars args proof

-- Continue after `namedPreclipFundedSiteValue%` and replace the final upper theorem.
open Lean Elab Term Meta in
local elab "selectedPlacementProperty%" : term => do
  let source ← getConstInfo ``selected_preclip_layout
  let indexed ← getConstInfo ``FundedDate.preclip_indexed_layout
  let funded ← getConstInfo ``fundedSiteOfIndexedLayout
  withLocalDeclD `chosenPlacement source.type fun selected => do
    let prop ← forallTelescope source.type fun args _ => do
      let lowerLayout := (source.value!.beta args).consumeMData
      unless lowerLayout.isAppOf indexed.name do throwError "expected the lower funded layout"
      let proof := mkAppN (← mkConstWithFreshMVarLevels funded.name) lowerLayout.getAppArgs
      let law := (← inferType proof).consumeMData
      unless law.isAppOf ``preclipSiteFormula && law.getAppNumArgs == 4 do throwError "expected the lower site formula"
      let pieces := law.getAppArgs
      unless pieces[3]!.isAppOf indexed.name do throwError "expected the named indexed placement"
      let body := mkAppN law.getAppFn (pieces.set! 3 (mkAppN selected args))
      mkForallFVars args body
    mkLambdaFVars #[selected] prop

private def selectedPlacementSiteProperty := selectedPlacementProperty%

open Lean Elab Term Meta in
local elab "originalSelectedPlacementValue%" : term => do
  return (← getConstInfo ``selected_preclip_layout).value!

open Lean Elab Term Meta in
local elab "selectedPlacementBodyEq%" : term => do
  let source ← getConstInfo ``selected_preclip_layout
  let named ← mkConstWithFreshMVarLevels source.name
  let level ← getLevel source.type
  return mkAppN (mkConst ``Eq [level]) #[source.type,source.value!,named]

private theorem selectedPlacementBodyEq : selectedPlacementBodyEq% := rfl

private theorem selectedPreclipSiteOnBody : selectedPlacementSiteProperty (no_implicit_lambda% originalSelectedPlacementValue%) :=
  no_implicit_lambda% namedPreclipFundedSiteValue%

open Lean Elab Term Meta in
local elab "carryFundedSiteProperty%" : term => do
  let pred ← mkConstWithFreshMVarLevels ``selectedPlacementSiteProperty
  let equality ← mkConstWithFreshMVarLevels ``selectedPlacementBodyEq
  let lower ← mkConstWithFreshMVarLevels ``selectedPreclipSiteOnBody
  let some (_,original,named) := (← inferType equality).eq? | throwError "expected equality of complete placements"
  let transfer ← mkCongrArg pred equality
  return mkAppN (mkConst ``Eq.mp [.zero]) #[mkApp pred original, mkApp pred named, transfer, lower]

private theorem selectedPreclipSiteOnNamedLayout : selectedPlacementSiteProperty @selected_preclip_layout :=
  no_implicit_lambda% carryFundedSiteProperty%


/- Preserve the signed and settled measurements of the original local row as a
single named proposition while specializing the purchased calendar data. -/
open Lean Elab Term Meta in
local elab "calendarOriginalMeasurementBody%" : term => do
  let row ← getConstInfo ``Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.calendarRow_through
  forallTelescope row.type fun args equation => do
    let tail := args.extract (args.size - 8) args.size
    let names ← tail.mapM fun x => return (← x.fvarId!.getDecl).userName
    unless names == #[`layout, `site, `dense, `inside, `strict, `published, `run, `settle] do
      throwError "unexpected dated row operands: {names}"
    unless equation.isAppOfArity ``Eq 3 do throwError "expected the dated row equality"
    let measured ← mkForallFVars (args.extract (args.size - 2) args.size) equation
    let family ← mkLambdaFVars (args.extract 0 (args.size - 6)) measured
    if family.hasFVar then throwError "a row measurement depends on a discarded guard proof"
    return family

private def calendarOriginalMeasurements := calendarOriginalMeasurementBody%

open Lean Elab Term Meta in
local elab "calendarOriginalGuardedRowType%" : term => do
  let row ← getConstInfo ``Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.calendarRow_through
  forallTelescope row.type fun args _ => do
    let family ← mkConstWithFreshMVarLevels ``calendarOriginalMeasurements
    let measured := mkAppN family (args.extract 0 (args.size - 6))
    mkForallFVars (args.extract 0 (args.size - 2)) measured

private theorem calendarRowThroughNamed : calendarOriginalGuardedRowType% :=
  @Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.calendarRow_through

/-- The middle guard reads socket q on the first actual post-date role sheet. -/
private theorem calendarMidAddress_socket {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h w ell unitCost bits first : ℕ)
    (site : Fin (siteLast h (2^v.W) k + 1)) (date : Fin (events v.mesh).length)
    (socket : Fin v.widePacketDegree) :
    v.calendarMidAddress h w ell unitCost bits first site date socket =
      (v.wideDated h w ell unitCost).roleStart
        ((v.wideSpillDates h w ell unitCost bits first).roleRoot
          (v.wideSpillRankEnd h w bits first) 0) date.succ + 1 +
        (finProdFinEquiv (site, socket)).val := by
  simp only [calendarMidAddress, DatedRoleSheets.sheet, DatedRoleSheets.sink,
    Fin.val_zero, Nat.zero_mul, Nat.add_zero, WideCPU.SpillDates.dateRole]
  rfl


section
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h w ell unitCost bits first : ℕ)
    (site : Fin (siteLast h (2^v.W) k + 1)) (date : Fin (events v.mesh).length)
    (socket : Fin v.widePacketDegree)
local notation "onSheet" => (v.wideDated h w ell unitCost).roleStart
  ((v.wideSpillDates h w ell unitCost bits first).roleRoot (v.wideSpillRankEnd h w bits first) 0)
  date.succ + 1 + (finProdFinEquiv (site, socket)).val
local notation "onCalendar" => v.calendarMidAddress h w ell unitCost bits first site date socket

/-- Transfer the strict bound at this single addressed socket. -/
private theorem calendarSocketBound {radix cap : ℕ} {mem : ℕ → Fin radix} (onRole : (mem onSheet).val < cap) :
    (mem onCalendar).val < cap := by
  simpa only [calendarMidAddress_socket] using onRole

/-- Transfer the rank data of this same socket at a fixed bit. -/
private theorem calendarSocketPublished {radix index : ℕ} {published : Prop} {mem : ℕ → Fin radix}
    (onRole : published ↔ index < (mem onSheet).val) :
    published ↔ index < (mem onCalendar).val := by
  simpa only [calendarMidAddress_socket] using onRole

end

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


section
variable (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (statesAt : states) (site : Fin (siteLast h d k+1)) (externalBits : D→Bool) (returned : Memory (G).W)
local notation "voteAt" => v.wide_routed_attempt_on_visit h width S arenaRoom perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le Sfit routeAge support.size.widthFloor support.size.words path date day
local notation "x₀" => valAt statesAt site date.castSucc
local notation "y₀" => valAt statesAt site date.succ

private abbrev calendarAttemptContractionFromPins :=
  v.calendarRowThroughNamed (F:=F) h width ell unit v.maxBits rom S ((g).romEnd rom) ((g).workEnd S)
    first G time site date (control.spillRead site date) (control.signedRead site date)
    (control.mode site date) control.tag control.lane returned e record externalBits
    day _ _ (matrixAt date) voteAt x₀ y₀

open Lean Elab Term in
local elab "purchasedLocalRun" "[" values:term,* "]" : term => do
  let mut args := #[]
  for value in values.getElems do args := args.push (← elabTerm value none)
  return mkAppN (← Meta.mkConstWithFreshMVarLevels ``wide_selected_local_return) args

open Lean Elab Term in
local elab "returnedMemoryAt " paid:ident : term => do
  let mut proof ← Meta.getFVarFromUserName paid.getId
  for _ in [:3] do
    let some form ← Meta.whnfUntil (← Meta.inferType proof) ``And | throwError "expected funded observations"
    proof := mkAppN (Lean.mkConst ``And.right) (form.getAppArgs.push proof)
  let some form ← Meta.whnfUntil (← Meta.inferType proof) ``Exists | throwError "expected the returned memory"
  return mkAppN (Lean.mkConst ``Exists.choose form.getAppFn.constLevels!) (form.getAppArgs.push proof)

private abbrev calendarAttemptSelectedBits :=
  let _purchased := purchasedLocalRun [F,(inferInstance : Field F),k,p,q,Q,σ,Λ,κ,A,v,
    m,ell,short,u,δ,ξ,v.calendarUnit,N,x,cpu,v.calendarUnit_rate,support,prices,C,pricePos,buy,
    groupsFit,metadata,lanesFit,(rout).catalyst,e,perm,tag,path]
  let _returned := returnedMemoryAt _purchased
  v.calendarAttemptContractionFromPins m ell short u δ ξ x cpu control support routeAge
    e perm i date a day statesAt site externalBits _returned
end

variable (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (ok : kept) (words : wordTable) (q : states) (site : Fin (siteLast h d k+1))
local notation "voteAt" => v.wide_routed_attempt_on_visit h width S arenaRoom perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le Sfit routeAge support.size.widthFloor support.size.words path date day
local notation "x₀" => valAt q site date.castSucc
local notation "y₀" => valAt q site date.succ

/-- Fix the true two matrices, the originally selected path's neighboring
states, the returned paid memory and its literal four bit banks. The remaining
arguments are the intermediate aperture and the two local measurements. -/
abbrev calendarAttemptContraction :=
  v.calendarAttemptSelectedBits m ell short u δ ξ x cpu control support routeAge
    prices pricePos groupsFit metadata lanesFit buy e perm i tag date a day q site (data ok words q)


open Lean Elab Term Meta in
local elab "applyCalendarProducer% " producer:ident "[" values:term,* "]" : term => do
  let format ← getFVarFromUserName `v
  let some formatType ← whnfUntil (← inferType format) ``FixedProtocolFormat
    | throwError "expected the dated protocol format"
  let name ← resolveGlobalConstNoOverload producer
  let mut fn := mkAppN (← mkConstWithFreshMVarLevels name) formatType.getAppArgs
  for value in values.getElems do fn := mkApp fn (← elabTerm value none)
  return fn


/- Read the concrete memory already named by the numerical socket statement. -/
open Lean Elab Term Meta in
local elab "transportCalendarSocket% " producer:ident "(" geometry:term,* ")" "(" fact:term ")" : term => do
  let printed ← elabTerm fact none
  let typ ← inferType printed
  let equivalence ← whnfUntil typ ``Iff
  let (condition, inequality) := match equivalence with
    | some eqv => (some eqv.getAppArgs[0]!, eqv.getAppArgs[1]!)
    | none => (none, typ)
  let some lt ← whnfUntil inequality ``LT.lt | throwError "expected a strict numerical socket inequality"
  let lr := lt.getAppArgs
  let val := if condition.isSome then lr.back! else lr[lr.size-2]!
  let entry ← match val with
    | .proj _ _ x => pure x
    | _ =>
      if val.isAppOf ``Fin.val then pure val.getAppArgs.back!
      else throwError "expected a numeral read from physical memory"
  let .app mem _ := entry | throwError "expected a physical memory read"
  let some word ← whnfUntil (← inferType entry) ``Fin | throwError "expected a finite memory word"
  let format ← getFVarFromUserName `v
  let some formatType ← whnfUntil (← inferType format) ``FixedProtocolFormat
    | throwError "expected the dated protocol format"
  let n ← resolveGlobalConstNoOverload producer
  let mut result := mkAppN (← mkConstWithFreshMVarLevels n) formatType.getAppArgs
  for arg in geometry.getElems do result := mkApp result (← elabTerm arg none)
  let operands := match condition with
    | none => #[word.getAppArgs.back!, lr.back!, mem, printed]
    | some claim => #[word.getAppArgs.back!, lr[lr.size-2]!, claim, mem, printed]
  return mkAppN result operands

open Lean Elab Term Meta in
local elab "originalSocket% " arg:ident " ↦ " body:term : term <= expected => do
  let .forallE _ domain _ _ ← whnfForall expected | throwError "expected an original socket family"
  withLocalDeclD arg.getId domain fun row => do
    mkLambdaFVars #[row] (← elabTerm body none)
open Lean Elab Term Meta in
local elab "applyCalendarMeasurements% " "(" fn:term ")" "[" values:term,* "]" : term => do
  let mut result ← elabTerm fn none
  let mut type ← inferType result
  for value in values.getElems do
    let .forallE _ dom body _ ← whnfForall type | throwError "a dated measurement operand is missing"
    let arg ← elabTerm value (some dom)
    result := mkApp result arg
    type := body.instantiate1 arg
  return result

local notation "layout" => applyCalendarProducer% selected_preclip_layout [κ, A, v, m, ell, short, u, δ, ξ, unit, N, x, cpu, v.calendarUnit_rate, support, prices, C, pricePos, buy, groupsFit, metadata, lanesFit, (rout).catalyst, e, perm, tag, path, routeAge, height, date, a, day]
local notation "siteLaw" => applyCalendarProducer% selectedPreclipSiteOnNamedLayout [κ, A, v, m, ell, short, u, δ, ξ, unit, N, x, cpu, v.calendarUnit_rate, support, prices, C, pricePos, buy, groupsFit, metadata, lanesFit, (rout).catalyst, e, perm, tag, path, routeAge, height, date, a, day]
local notation "midAddress" => v.calendarMidAddress h width ell unit v.maxBits first site date

open Lean Elab Term Meta in
local elab "preclipPlacementType% " value:term : term => do
  inferType (← elabTerm value none)

open Lean Elab Term Meta in
local elab "paidPlacementSite% " issued:term " on " chosen:ident : term => do
  let law := (← inferType (← elabTerm issued none)).consumeMData
  unless law.isAppOf ``preclipSiteFormula && law.getAppNumArgs == 4 do
    throwError "expected the selected placement's four-argument physical site formula"
  return mkApp law.appFn! (← getFVarFromUserName chosen.getId)

local notation "physicalDegree" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "physicalCap" => v.wideNeighborCap width unit
local notation "roleAtSocket" port:arg => (g).roleStart
  ((v.wideSpillDates h width ell unit v.maxBits first).roleRoot
    (v.wideSpillRankEnd h width v.maxBits first) 0) date.succ + 1 +
      (finProdFinEquiv (site,port)).val

private abbrev calendarMeasurementsOnPhysicalSheet (externalBits : D → Bool)
    (returned : Memory W) (placement : preclipPlacementType% layout)
    (placementSite : paidPlacementSite% siteLaw on placement)
    (strict : ∀ port : Fin physicalDegree,
      (returned (roleAtSocket port)).val < 2^(v.wideNeighborDigits width unit+1))
    (published : ∀ cell : Fin (physicalDegree*physicalCap), (site,cell) ∈ Set.range placement ↔
      ((finProdFinEquiv : Fin physicalDegree × Fin physicalCap ≃ Fin (physicalDegree*physicalCap)).symm cell).2.val <
        (returned (roleAtSocket (finProdFinEquiv.symm cell).1)).val) :=
  applyCalendarMeasurements% (v.calendarAttemptContractionFromPins m ell short u δ ξ x cpu control support routeAge
    e perm i date a day q site externalBits returned)
    [placement, placementSite, (fun _ => rfl), ((SignedSites.calendar_words v m ell short unit cpu).2 site date),
     (originalSocket% port ↦ transportCalendarSocket% calendarSocketBound
       (v,h,width,ell,unit,v.maxBits,first,site,date,port) (strict port)),
     (originalSocket% cell ↦ transportCalendarSocket% calendarSocketPublished
       (v,h,width,ell,unit,v.maxBits,first,site,date,(finProdFinEquiv.symm cell).1) (published cell))]

/- Keep the local return type in the coordinate system of its physical
placement before substituting the purchased placement and its site law. -/
open Lean Elab Term Meta in
local elab "physicalSheetMeasurement% " "[" families:ident,* "]" : term => do
  let sheet ← getConstInfo ``calendarMeasurementsOnPhysicalSheet
  let mut sheetType := sheet.type
  let mut physicalBinderCount := 0
  while let .forallE n _ rest _ := sheetType do
    physicalBinderCount := physicalBinderCount + 1
    sheetType := rest
    if n == `published then break
  forallBoundedTelescope sheet.type (some physicalBinderCount) fun args residual => do
    let physicalArgs := args.extract (args.size - 6) args.size
    let physicalBinderNames ← physicalArgs.mapM fun x => return (← x.fvarId!.getDecl).userName
    unless physicalBinderNames == #[`externalBits, `returned, `placement, `placementSite, `strict, `published] do
      throwError "unexpected physical measurement inputs: {physicalBinderNames}"
    let placementArgs := args.extract 0 (args.size - 2)
    match families.getElems.toList with
    | [] =>
      let body ← mkLambdaFVars placementArgs residual
      if body.hasFVar then throwError "a physical measurement depends on a socket guard proof"
      return body
    | [family] =>
      let n ← resolveGlobalConstNoOverload family
      let measured := mkAppN (← mkConstWithFreshMVarLevels n) placementArgs
      mkForallFVars args measured
    | _ => throwError "expected at most one physical measurement family"

private def calendarPhysicalMeasurementResult := physicalSheetMeasurement% []

private theorem calendarPhysicalMeasurementsThrough :
    physicalSheetMeasurement% [calendarPhysicalMeasurementResult] :=
  @calendarMeasurementsOnPhysicalSheet


-- The source family supplies the exact physical-memory expression, including its
-- implicit existential predicate. Section arguments come from the checked helper's telescope.
open Lean Elab Term Meta in
local elab "readPhysicalMeasurements% " helper:ident "(" external:term ")" "(" placementExpr:term ")"
    "(" placeSite:term ")" "(" strictFamily:term ")" "(" pubFamily:term ")" : term => do
  let strict ← elabTerm strictFamily none
  let memory ← forallBoundedTelescope (← inferType strict) (some 1) fun _ inequality => do
    let some lt ← whnfUntil inequality ``LT.lt | throwError "expected the strict physical socket bound"
    let xs := lt.getAppArgs
    let lhs := xs[xs.size-2]!
    let word ← match lhs with
      | .proj _ _ word => pure word
      | _ => if lhs.isAppOf ``Fin.val then pure lhs.getAppArgs.back! else throwError "expected a finite word value"
    let .app memory _ := word | throwError "expected a physical socket read"
    pure memory
  let name ← resolveGlobalConstNoOverload helper
  let format ← getFVarFromUserName `v
  let some fty ← whnfUntil (← inferType format) ``FixedProtocolFormat | throwError "expected the fixed protocol format"
  let initial := fty.getAppArgs
  let mut fn := mkAppN (← mkConstWithFreshMVarLevels name) initial
  let mut ty := (← getConstInfo name).type
  for _ in [:initial.size] do ty := ty.bindingBody!
  while let .forallE binder _ rest _ := ty do
    if binder == `externalBits then break
    fn := mkApp fn (← getFVarFromUserName binder)
    ty := rest
  let .forallE `externalBits _ _ _ := ty | throwError "missing the external bit bank"
  return mkAppN fn #[← elabTerm external none, memory, ← elabTerm placementExpr none, ← elabTerm placeSite none,
    strict, ← elabTerm pubFamily none]

local notation "physicalStrict" => applyCalendarProducer% selected_preclip_strict
  [κ, A, v, m, ell, short, u, δ, ξ, unit, N, x, cpu, v.calendarUnit_rate, support, prices, C, pricePos,
   buy, groupsFit, metadata, lanesFit, (rout).catalyst, e, perm, tag, path, routeAge, height, date, a, day, site]
local notation "physicalPublished" => applyCalendarProducer% selected_preclip_published
  [κ, A, v, m, ell, short, u, δ, ξ, unit, N, x, cpu, v.calendarUnit_rate, support, prices, C, pricePos,
   buy, groupsFit, metadata, lanesFit, (rout).catalyst, e, perm, tag, path, routeAge, height, date, a, day, site]

/-- The chosen paid memory's original socket families discharge both numerical
premises. The caller supplies the signed row value and its settlement value. -/
abbrev calendarAttemptMeasurements :=
  readPhysicalMeasurements% calendarPhysicalMeasurementsThrough (data ok words q)
    (layout) (siteLaw) (physicalStrict) (physicalPublished)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
