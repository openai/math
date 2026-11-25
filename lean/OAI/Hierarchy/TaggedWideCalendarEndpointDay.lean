import OAI.Hierarchy.TaggedWideFundedRankedSteps
import OAI.Hierarchy.TaggedWideCalendarEndpointFields
import OAI.Hierarchy.TaggedWireActualRoutedSchedule

namespace OAI
/-! # Individual dated observations of the actual funded signed calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows CatalystArchive
open Tagged Tagged.WideStack TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMEmit
open ProtocolRAMReportedPorts PurchaseFrozen
open scoped Classical BigOperators
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option cleanup.letToHave false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (tapeSize : ℕ)
    (π : Equiv.Perm (Fin (2^x.h))) (input : Boot.Tape x.h (2^v.W)) (m ell short unitCost : ℕ)
local notation "b" => (v.widePlacement x.h x.w).catalogue
local notation "jobs" => v.wideJobs
local notation "geom" => typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
local notation "slots" => purchaseSlots x.h v.W k jobs ell
local notation "reserve" => fuel v.mesh*x.w
variable (raw : Fin (b).rows→ ProtocolRAMEmit.Row)
    (geometry : Geometry (boardLayout x.h (2^v.W) k x.w reserve) v.radius 1 raw)
    (actual : v.FundedCutRows x.h x.w tapeSize π input raw geometry unitCost)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates x.h v.W k jobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k jobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
open CoreBoard.PhysicalTerm Tagged.WideControlJoin WideCalendarSites HistoryRoles
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune

local notation "days" => events v.mesh
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (room : cpu.SiteRoom)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
variable (a : SignedSites v m ell short δ ξ unitCost cpu)
local notation "Z" => a.schedule
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "Ex" => OpenPins x.h x.w ((Z).nativeRouting D).catalyst
local notation "Se" => Fin ((Z).nativeRouting D).selectors
local notation "cap" => v.widePrivateUnit unitCost*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) («W»:=v.W) (k:=k) (attempts:=jobs)
  v.mesh unitCost v.keepLimit (fuel v.mesh) x.w
local notation "n" => ((days).length+1)*Fintype.card ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r))

variable (perm : Equiv.Perm (Tagged.Row x.h)) (i : Fin (((Z).nativeRouting D).count perm))
local notation "branch" => (Fintype.equivFin (Path slot days ((v.wideOrigin x.h x.w size seed) perm))).symm i
local notation "original" => (Z).reported perm branch
local notation "time" => v.wideHistoryGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.history
local notation "rout" => (Z).nativeRouting D
local notation "accept" => ((rout).links ⟨perm,i⟩).Keep (2^x.h)
local notation "flagAt" => (lay).pruneScratch+(lay).pruneRows
local notation "cursor" => CalendarTape.Prefix.cursorSlot («slot»:=slot) (events:=days) (x₀:=(v.wideOrigin x.h x.w size seed) perm)
local notation "hs" => CalendarTape.Prefix.atCursor (CalendarTape.Prefix.start : CalendarTape.Prefix slot days ((v.wideOrigin x.h x.w size seed) perm)
  days ((v.wideOrigin x.h x.w size seed) perm))
local notation "ws" => CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "branchAt" => CalendarTape.Prefix.histories (CalendarTape.Prefix.start : CalendarTape.Prefix slot days ((v.wideOrigin x.h x.w size seed) perm)
  days ((v.wideOrigin x.h x.w size seed) perm)) branch

variable {v x tapeSize π input m ell short unitCost raw geometry actual prices pricePos buy
  groupsFit metadata lanesFit cpu room a perm i}
variable {mem before initial out : Memory W}
local notation "signedBoard" => RowGeometry x.h (2^v.W) k x.w reserve v.radius 1
variable (same : reportGeometry perm original = (⟨(b).rows,raw,geometry⟩ : signedBoard))
local notation "sameRows" => congrArg
  (fun r : signedBoard => (⟨r.1,r.2.1⟩ : CalendarTerms.RowBoard)) same
local notation "imageType" => FundedCutRows.WindowReceipt v x tapeSize π input m ell short unitCost
  raw geometry actual prices pricePos buy groupsFit metadata lanesFit cpu.room room.purchase mem before initial out
local notation "sourceAt" ok:arg => FundedCutRows.rowData v x tapeSize π input m ell short unitCost
  raw geometry actual prices pricePos buy groupsFit metadata ok lanesFit
local notation "rankAt" ok:arg => CalendarTerms.RankedRows.onBranch Z perm i sameRows (sourceAt ok)
local notation "rankFacts" ex:arg sel:arg ok:arg place:arg => CalendarTerms.RankedRows.Endpoints Z (geom).index G time
  a.enter a.finish a.step perm i ex sel ((G).terminal out) (rankAt ok) place

variable (image : imageType) (ex : Ex → Bool) (sel : Se → Bool)
    (ok : geometry.links.Keep (2^x.h)) (place : PartyBit cursor ws days hs branchAt ↪ Fin n)
local notation "ranking" => rankAt ok
local notation "stepOp" => CalendarTape.Prefix.atStep ((Z).width perm) ((Z).operator perm)
local notation "replayed" => cursorReport perm ((Z).width perm) ((Z).reported perm) branchAt
local notation "wordTable" => (e : Fin (replayed).edges) → Fin (2^((replayed).rows e).width)
local notation "choices" => SiteChoices cursor ws days hs branchAt
local notation "view" => v.wideHistoryUnit unitCost*x.w
local notation "observed" d:arg q:arg s:arg j:arg => TypedWiring.value (a.step s j)
  (CalendarTerms.readPins (B:=G) (ranking).numbering ex sel ((G).terminal out)
    (nativePins («view»:=view) (geom).index (replayed).rows (ranking).positive (ranking).stage
      (ranking).installed (ranking).cap d (placedBits cursor ws days hs branchAt place q)))
local notation "valueAt" q:arg s:arg j:arg => datedState cursor ws s days hs branchAt j (q s)
local notation "matrixAt" j:arg => indexedStep cursor ws stepOp days hs branchAt j


def FundedCutRows.DayCheck (_image : imageType) (j : Fin (days).length) : Prop :=
  ∀ (kept : geometry.links.Keep (2^x.h)) (d : wordTable) (q : choices) s,
    TypedWiring.value (a.step s j)
      (CalendarTerms.readPins (B:=G) (rankAt kept).numbering ex sel ((G).terminal out)
        (nativePins («view»:=view) (geom).index (replayed).rows (rankAt kept).positive (rankAt kept).stage
          (rankAt kept).installed (rankAt kept).cap d (placedBits cursor ws days hs branchAt place q))) =
      (matrixAt j) s (valueAt q s j.castSucc) (valueAt q s j.succ)

theorem FundedCutRows.check_of_days (all : ∀j,FundedCutRows.DayCheck (a:=a) (room:=room) (perm:=perm)
    (i:=i) same ex sel place image j) :
    FundedCutRows.EndpointCheck (a:=a) (room:=room) (perm:=perm) (i:=i) same image ex sel place .steps := by
  intro kept
  apply FundedCutRows.ranked_steps_of_indexed (a:=a) (perm:=perm) (i:=i) same ex sel kept place
  intro d q s j
  exact all j kept d q s

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
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

local notation "runAt" => v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "image" => (runAt).2.2.2.choose_spec.2.2.2.2
local notation "same" => (v.wide_selected_geometry m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path)
local notation "place" => v.wideCalendarPartyPlace m ell short u δ ξ x cpu Z perm i height (fun _=>rfl)

-- The selected CPU already carries the funding indices used by DayCheck.
open Lean Elab Term in
local elab "purchasedLocalRun" "[" values:term,* "]" : term => do
  let mut args := #[]
  for value in values.getElems do args := args.push (← elabTerm value none)
  return mkAppN (← Meta.mkConstWithFreshMVarLevels ``wide_selected_local_return) args

/- The spill scan's result predicate and its native register type are the
reducible fields of the recorded operation. Keep those two fields while
projecting an existential, so unused constructor proofs stay in their producer. -/
open Lean in
private def recordedChoiceType (family : Lean.Expr) : Lean.Expr :=
  family.replace fun node =>
    if node.isAppOfArity ``SpillDataType 2 then some node.getAppArgs[0]!
    else if node.isAppOf ``SpillFields && node.getAppNumArgs ≥ 7 then
      let fields := node.getAppArgs
      some (mkAppN fields[5]! (fields.extract 7 fields.size))
    else none

open Lean Elab Term in
local elab "selectedWindowAt " native:ident : term => do
  let mut proof ← Meta.getFVarFromUserName native.getId
  for _ in [:3] do
    let form ← Meta.whnf (← Meta.inferType proof)
    unless form.isAppOf ``And do throwError "expected the funded return observations"
    proof := Lean.Expr.proj ``And 1 proof
  let witness := recordedChoiceType (← Meta.whnf (← Meta.inferType proof))
  unless witness.isAppOf ``Exists do throwError "expected the single returned memory"
  proof := mkAppN (Lean.mkConst ``Classical.choose_spec witness.getAppFn.constLevels!) (witness.getAppArgs.push proof)
  for _ in [:4] do
    let form ← Meta.whnf (← Meta.inferType proof)
    unless form.isAppOf ``And do throwError "expected the retained register observations"
    proof := Lean.Expr.proj ``And 1 proof
  return proof

open Lean Elab Term in
local elab "dayOnCheckedWindow " witness:ident " installed " "[" mounted:term,* "]"
    " at " "[" inputs:term,* "]" " day " dayValue:ident : term => do
  let receipt ← Meta.getFVarFromUserName witness.getId
  let recordType ← Meta.whnf (← Meta.inferType receipt)
  unless recordType.isAppOf ``FundedCutRows.WindowReceipt do throwError "expected the actual purchased window receipt"
  let captured := recordType.getAppArgs
  unless captured.size == 38 do throwError "unexpected window interface"
  let mut args := captured.extract 0 32
  for arg in mounted.getElems do args := args.push (← elabTerm arg none)
  args := args ++ captured.extract 34 38
  for arg in inputs.getElems do args := args.push (← elabTerm arg none)
  let event ← Meta.getFVarFromUserName dayValue.getId
  return mkAppN (← Meta.mkConstWithFreshMVarLevels ``FundedCutRows.DayCheck) ((args.push receipt).push event)

/- Build the closed physical predicate as one kernel-checked definition. The
indices are taken from the selected return before closing the calendar context. -/
open Lean Elab Command Term Meta in
local elab "definePurchasedDay " body:term : command => do
  let checkedDefinitionName :=  (← getCurrNamespace) ++ `calendarDayRead
  runTermElabM fun context => do
    let result ← withoutErrToSorry <| elabTerm body none
    synthesizeSyntheticMVarsNoPostponing
    let closed ← mkLambdaFVars context (← instantiateMVars result) (usedOnly := true)
    let value ← Term.levelMVarToParam closed
    let type ← instantiateMVars (← inferType value)
    if value.hasFVar || value.hasMVar || value.hasSorry || type.hasFVar || type.hasMVar || type.hasSorry then
      throwError "the selected chronological date is not closed"
    let levels := (collectLevelParams {} type).params.toList
    addDecl (.defnDecl {
      name := checkedDefinitionName
      levelParams := levels
      type := type
      value := value
      hints := .regular 1
      safety := .safe
    })
    addDocStringCore checkedDefinitionName "The physical row equation at one original date of the selected, purchased execution."

definePurchasedDay (fun (_j : Fin (es).length) =>
  let _purchased := purchasedLocalRun [F,(inferInstance : Field F),k,p,q,Q,σ,Λ,κ,A,v,
    m,ell,short,u,δ,ξ,v.calendarUnit,N,x,cpu,v.calendarUnit_rate,support,prices,C,pricePos,buy,
    groupsFit,metadata,lanesFit,(rout).catalyst,e,perm,tag,path]
  let _window := selectedWindowAt _purchased

  let _same := v.wide_selected_geometry m ell short u δ ξ v.calendarUnit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path
  dayOnCheckedWindow _window installed [N,cpu,room,sites,perm,i] at [_same,e,record,place] day _j)


/- Pass the exact fields of each authenticated date to the native all-dates
rule. The rule consumes the common selected window and the daywise proof. -/
open Lean Elab Tactic in
local elab "closeCheckedDates " daily:ident : tactic => withMainContext do
  let allDates ← Meta.getFVarFromUserName daily.getId
  let input ← Meta.inferType allDates
  Meta.forallBoundedTelescope input (some 1) fun _ dayTargetType => do
    let some checked ← Meta.whnfUntil dayTargetType ``FundedCutRows.DayCheck
      | throwError "expected the checked chronological day"
    let evidence := checked.getAppArgs
    unless evidence.size == 48 do throwError "unexpected native per-day interface"
    let fields := evidence.extract 0 43 ++ #[evidence[46]!,evidence[43]!,evidence[44]!,evidence[45]!,allDates]
    let conclusion := mkAppN (← Meta.mkConstWithFreshMVarLevels ``FundedCutRows.check_of_days) fields
    (← getMainGoal).assign conclusion
    replaceMainGoal []

theorem calendar_steps_of_dates (reads : ∀j,v.calendarDayRead (C:=C) m ell short u δ ξ x cpu room control support
    routeAge prices pricePos groupsFit metadata lanesFit buy e perm i tag height j) :
    v.wideCalendarEndpointField (C:=C) m ell short u δ ξ x cpu room control support
      Z (fun _ _=>rfl) prices pricePos groupsFit metadata lanesFit buy e perm i tag height
      (fun _=>rfl) .steps := by
  closeCheckedDates reads

-- Omit full physical-day signatures from the optional premise-search index.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry (Lean.LibrarySuggestions.nameDenyListExt.addEntry (Lean.LibrarySuggestions.nameDenyListExt.addEntry env "DayCheck") "check_of_days") "calendar_steps_of_dates"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
