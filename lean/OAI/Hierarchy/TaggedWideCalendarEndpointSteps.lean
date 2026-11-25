import OAI.Hierarchy.TaggedWideCalendarAttemptVote
import OAI.Hierarchy.TaggedWideCalendarAttemptSpill
import OAI.Hierarchy.ProbeFixedFundedCalendarFeedDay

namespace OAI
/-! # Native site coefficient at every date of the purchased original path -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
set_option maxRecDepth 12288
set_option maxHeartbeats 2200000
open private calendarOriginalMeasurements calendarPhysicalMeasurementResult preclipSiteFormula from
  OAI.Hierarchy.TaggedWideCalendarAttemptAt
open private originalSettlementWithChart physicalSettlementOnPaidChart paidReadSiteChart paidSettlementChart_eq from
  OAI.Hierarchy.TaggedWideCalendarAttemptSpill

open Lean Elab Term Meta in
local elab "originalSettlementFamily%" : term => do
  let source ← getConstInfo ``calendarOriginalMeasurements
  forallTelescope source.type fun args _ => do
    let .forallE `run _ afterRun _ := (source.value!.beta args).consumeMData
      | throwError "expected the signed premise of the original row"
    let .forallE `settle settlement _ _ := afterRun.consumeMData
      | throwError "expected the second, settlement premise of the original row"
    if settlement.hasLooseBVars then throwError "the settlement predicate depends on the signed proof"
    mkLambdaFVars args settlement

private def endpointOriginalSettlement := originalSettlementFamily%

-- Replace the head of a folded result while preserving its arguments and the
-- telescope around it. The final public type is never opened at a concrete path.
open Lean Elab Term Meta in
local elab "settlementFromFold% " producer:ident previous:ident projection:ident : term => do
  let src ← getConstInfo (← resolveGlobalConstNoOverload producer)
  let oldName ← resolveGlobalConstNoOverload previous
  let newHead ← mkConstWithFreshMVarLevels (← resolveGlobalConstNoOverload projection)
  let fromType := src.name == ``calendarAttemptMeasurements
  let rec build (term : Lean.Expr) : TermElabM Lean.Expr := do
    match term with
    | .mdata _ body => build body
    | .lam n domain body bi =>
      if fromType then throwError "unexpected lambda in the selected theorem type"
      return .lam n domain (← build body) bi
    | .forallE n domain body bi =>
      unless fromType do throwError "expected a folded original result"
      return .lam n domain (← build body) bi
    | residual =>
      unless residual.isAppOf oldName do throwError "expected the folded result {oldName}"
      return mkAppN newHead residual.getAppArgs
  build (if fromType then src.type else src.value!)

private def endpointPhysicalSettlement :=
  settlementFromFold% calendarPhysicalMeasurementResult calendarOriginalMeasurements endpointOriginalSettlement

-- Reinsert the unique original chart in the already-abstracted predicate. The
-- rfl proof verifies the whole second predicate, including both exit and state binders.
open Lean Elab Term Meta in
local elab "restoreEndpointChart% " mode:ident : term => do
  let original ← getConstInfo ``calendarOriginalMeasurements
  forallTelescope original.type fun args _ => do
    let .forallE `run _ tail _ := (original.value!.beta args).consumeMData | throwError "expected the signed premise"
    let .forallE `settle domain _ _ := tail.consumeMData | throwError "expected the original settlement premise"
    let some originalChart := Lean.Expr.find? (·.isAppOfArity ``Hierarchy.ProbeStage.CoreBoard.LedgerStep.siteChart 5) domain
      | throwError "expected the authentic original row chart"
    if originalChart.hasLooseBVars then throwError "the chart depends on an exit or intermediate state"
    let kept := args.extract 0 (args.size-2)
    let pred := mkAppN (← mkConstWithFreshMVarLevels ``originalSettlementWithChart) kept
    let lhs := mkApp pred originalChart
    let rhs := mkAppN (← mkConstWithFreshMVarLevels ``endpointOriginalSettlement) args
    if mode.getId == `statement then mkForallFVars args (← mkEq lhs rhs)
    else mkLambdaFVars args (← mkEqRefl lhs)

private theorem restoredOriginalSettlement : restoreEndpointChart% statement :=
  no_implicit_lambda% (restoreEndpointChart% proof)

-- Transport the paid chart before instantiating the purchased path.
open Lean Elab Term Meta in
local elab "purchasedChartPhysicalEq% " mode:ident : term => do
  let sheet ← getConstInfo ``calendarPhysicalMeasurementResult
  forallTelescope sheet.type fun args _ => do
    let left := mkAppN (← mkConstWithFreshMVarLevels ``physicalSettlementOnPaidChart) args
    let right := mkAppN (← mkConstWithFreshMVarLevels ``endpointPhysicalSettlement) args
    if mode.getId == `statement then return ← mkForallFVars args (← mkEq left right)
    let original := (sheet.value!.beta args).consumeMData
    unless original.isAppOf ``calendarOriginalMeasurements do throwError "expected original dated measurements"
    let raw := original.getAppArgs
    let paid := args.back!
    let law := (← inferType paid).consumeMData
    unless law.isAppOfArity ``preclipSiteFormula 4 do throwError "expected the funded site proof"
    let #[sites,bits,lanes,placement] := law.getAppArgs | throwError "expected four funded layout operands"
    let some n ← whnfUntil sites ``Fin | throwError "expected finite physical sites"
    let some m ← whnfUntil lanes ``Fin | throwError "expected finite physical lanes"
    let chartEq := mkAppN (← mkConstWithFreshMVarLevels ``paidSettlementChart_eq)
      #[n.appArg!,m.appArg!,bits,placement,paid]
    let pred := mkAppN (← mkConstWithFreshMVarLevels ``originalSettlementWithChart) (raw.extract 0 (raw.size-2))
    let sameChart ← mkCongrArg pred chartEq
    let restore := mkAppN (← mkConstWithFreshMVarLevels ``restoredOriginalSettlement) raw
    mkLambdaFVars args (← mkEqTrans sameChart restore)

private theorem purchasedSettlement_eq : purchasedChartPhysicalEq% statement :=
  no_implicit_lambda% (purchasedChartPhysicalEq% proof)


open Lean Elab Term Meta in
local elab "calendarStoredApplication% " theoremName:ident "[" passed:term,* "]" : term => do
  let symbol ← resolveGlobalConstNoOverload theoremName
  let decl ← getConstInfo symbol
  let formatArgs := (← inferType (← getFVarFromUserName `v)).getAppArgs
  let mut values := #[]
  let mut arguments := #[]
  let mut signature := decl.type
  let provided := passed.getElems
  let mut index := 0
  repeat
    match signature with
    | .letE _ _ rhs body _ =>
      values := values.push (rhs.instantiateRev values)
      signature := body
    | .mdata _ body => signature := body
    | .forallE label _ body kind =>
      if kind == .default && index == provided.size then break
      let value ← if kind == .instImplicit then pure formatArgs[1]!
        else if kind != .default then
          if label == `q then pure formatArgs[4]! else getFVarFromUserName label
        else do
          let term := provided[index]!
          elabTerm term none
      if kind == .default then index := index+1
      values := values.push value
      arguments := arguments.push value
      signature := body
    | _ => break
  unless index == provided.size do throwError "unused explicit arguments for {symbol}"
  return mkAppN (← mkConstWithFreshMVarLevels symbol) arguments

open Lean Meta Elab Tactic in
local elab "applyPurchasedMeasurements " measured:term:max " vote " voted:term:max " spill " settled:term:max : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let row ← Term.elabTermAndSynthesize measured none
    let asRun ← Term.elabTermAndSynthesize voted none
    let paid ← Term.elabTermAndSynthesize settled none
    let physical := (← inferType row).consumeMData
    unless physical.isAppOf ``calendarPhysicalMeasurementResult do
      throwError "expected the selected physical calendar measurement"
    let coefficients := physical.getAppArgs
    let paidPredicate := mkAppN (← mkConstWithFreshMVarLevels ``physicalSettlementOnPaidChart) coefficients
    let requiredPredicate := mkAppN (← mkConstWithFreshMVarLevels ``endpointPhysicalSettlement) coefficients
    let same := mkAppN (← mkConstWithFreshMVarLevels ``purchasedSettlement_eq) coefficients
    let asSettle := mkAppN (mkConst ``Eq.mp [.zero]) #[paidPredicate, requiredPredicate, same, paid]
    goal.assign (mkApp2 row asRun asSettle)
    replaceMainGoal []

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
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

variable (routeAge : v.routingHeight≤h)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "Z" => v.routedSchedule h width S arenaRoom seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit routeAge support.size.widthFloor support.size.words
local notation "rout" => (Z).nativeRouting D
local notation "sites" => SignedSites.ofCalendar (cpu:=cpu) Z control v.calendarTerminalWidth
  (v.calendarTerminalPins x m ell short)
local notation "source" => fun _ : Fin (m+1)=>slots
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates h v.W k v.wideJobs slots ((menu).height i x) (count i)
local notation "Buy" => PurchaseList (F:=F) («C»:=C) menu x source target count
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

local notation "runAt" => v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "image" => (runAt).2.2.2.choose_spec.2.2.2.2
local notation "same" => (v.wide_selected_geometry m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path)
local notation "place" => v.wideCalendarPartyPlace m ell short u δ ξ x cpu Z perm i height (fun _=>rfl)

variable (word : v.PartyWordBounds h width unit)

/-- At an attempted date, contract the true signed vote with the elected
native settlement over the complete intermediate chord state. -/
theorem calendar_attempt_day
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (word : v.PartyWordBounds h width unit)
    (j : Fin (es).length) (a : Attempt) (onDate : (es).get j=.attempt a) :
    v.calendarDayRead («C»:=C) m ell short u δ ξ x cpu room control support routeAge prices pricePos
      groupsFit metadata lanesFit buy e perm i tag height j := by
  apply (v.calendarDayRead_iff («C»:=C) m ell short u δ ξ x cpu room control support routeAge prices pricePos
    groupsFit metadata lanesFit buy e perm i tag height j).2
  intro ok words assignment site
  applyPurchasedMeasurements (calendarStoredApplication% calendarAttemptMeasurements [v,m,ell,short,u,δ,ξ,x,cpu,control,support,
    routeAge,prices,pricePos,groupsFit,metadata,lanesFit,buy,e,perm,i,tag,height,j,a,onDate,ok,words,assignment,site])
    vote (calendarStoredApplication% calendar_attempt_vote [v,m,ell,short,u,δ,ξ,x,cpu,control,support,routeAge,prices,
      pricePos,groupsFit,metadata,lanesFit,buy,e,perm,i,tag,height,j,a,onDate,ok,words,assignment,site,word])
    spill (calendarStoredApplication% wide_calendar_spill_at [v,m,ell,short,u,δ,ξ,x,cpu,control,support,routeAge,prices,
      pricePos,groupsFit,metadata,lanesFit,buy,e,perm,i,tag,height,j,a,onDate,ok,words,assignment,site])

private theorem checkedDaysFromEvents (dates : List Hierarchy.ProtocolRAM.Calendar.Event) (readAt : Fin dates.length → Prop)
    (feedRows : ∀ j b, dates.get j = .feed b → readAt j)
    (attemptRows : ∀ j a, dates.get j = .attempt a → readAt j) :
    ∀ j, readAt j := by
  intro j
  cases eqn : dates.get j with
  | feed b => exact feedRows j b eqn
  | attempt a => exact attemptRows j a eqn

/-- The public date fixes the physical row. Its result on each retained
assignment is the indexed operator of the actual selected branch. -/
theorem calendar_day
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (word : v.PartyWordBounds h width unit)
    (j : Fin (es).length) :
    v.calendarDayRead («C»:=C) m ell short u δ ξ x cpu room control support routeAge prices pricePos
      groupsFit metadata lanesFit buy e perm i tag height j := by
  exact checkedDaysFromEvents es
    (v.calendarDayRead («C»:=C) m ell short u δ ξ x cpu room control support routeAge prices pricePos
      groupsFit metadata lanesFit buy e perm i tag height)
    (fun date b hd => calendarStoredApplication% calendar_feed_day [v,m,ell,short,u,δ,ξ,x,cpu,room,control,support,
      routeAge,prices,pricePos,groupsFit,metadata,lanesFit,buy,e,perm,i,tag,height,date,b,hd])
    (fun date a hd => calendarStoredApplication% calendar_attempt_day [v,m,ell,short,u,δ,ξ,x,cpu,room,control,support,
      routeAge,prices,pricePos,groupsFit,metadata,lanesFit,buy,e,perm,i,tag,height,word,date,a,hd]) j


/-- All dated entries of the chronological physical site matrix on the
original routed schedule and the returned CPU memory. -/
theorem calendar_endpoint_steps
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (word : v.PartyWordBounds h width unit) :
    v.wideCalendarEndpointField («C»:=C) m ell short u δ ξ x cpu room control support Z (fun _ _=>rfl)
      prices pricePos groupsFit metadata lanesFit buy e perm i tag height (fun _=>rfl) .steps := by
  exact calendarStoredApplication% calendar_steps_of_dates [v,m,ell,short,u,δ,ξ,x,cpu,room,control,support,
      routeAge,prices,pricePos,groupsFit,metadata,lanesFit,buy,e,perm,i,tag,height,
    (calendarStoredApplication% calendar_day [v,m,ell,short,u,δ,ξ,x,cpu,room,control,support,
      routeAge,prices,pricePos,groupsFit,metadata,lanesFit,buy,e,perm,i,tag,height,word])]


run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun prior =>
    "calendar_attempt_day" :: "calendar_day" :: "calendar_endpoint_steps" :: prior

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
