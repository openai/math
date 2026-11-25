import OAI.Hierarchy.TaggedWideCalendarDayOuterBits
import OAI.Hierarchy.ProbeFixedFundedCalendarFeedShapesDay
import OAI.Hierarchy.TaggedWideRankedSpillCarry
import OAI.Hierarchy.TaggedWideCalendarSpillShelfRoom

namespace OAI
/-! # The original feed chosen at a concrete funded calendar date -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ThreeFlat Routing Diagonal TraceWords
open LinearAlgebra.SpectralBooks.ChordGraph LinearAlgebra.SpectralBooks.SiteTensor
open Tagged Tagged.WideControlJoin Tagged.WideStack AdaptiveProbe ProbeStage CoreBoard HistoryRoles HistoryRoles.RoleProgram
open WireTelescope WireTelescope.PassMatrix WireTelescope.CalendarTape
open Computability.VPVNP.BurstRAM PrivateRAM WideCPU
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8000
set_option Elab.async false
set_option maxHeartbeats 600000

variable {F Ex Sel Data : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype Data]
    {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h w ell unitCost bits datedROM datedWork terminalROM terminalWork first : ℕ) (G : Gate)
local notation "siteCount" => siteLast h (2^v.W) k+1
local notation "degree" => v.widePacketDegree
local notation "es" => events v.mesh
local notation "digits" => v.wideNeighborDigits w unitCost
local notation "cap" => v.wideNeighborCap w unitCost
local notation "g" => v.wideDated h w ell unitCost
local notation "Z" => v.wideSpillDates h w ell unitCost bits first
local notation "rank" => v.wideSpillRankEnd h w bits first
local notation "sw" => (Z).roleRoot rank 2
local notation "cw" => (Z).spillControlWork rank
local notation "old" => (Z).preClip datedWork rank
local notation "now" => fun j=>(g).roleStart datedWork j.succ
local notation "leftOnly" => fun j=>(Z).dateRole rank j 1
local notation "rightOnly" => fun j=>(Z).dateRole rank j 2
local notation "panel" => v.wideSpillTurnPage h w bits datedROM terminalROM terminalWork first
    ((Z).endAt rank) old now leftOnly rightOnly
local notation "bs" => siteNumber h (2^v.W) k
local notation "room" => HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
    v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) w
local notation "ports" => (shelfSlot (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler)
local notation "seats" => WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "V" => SitePins Ex Sel Data G
local notation "mid" => Fin (degree*cap)
local notation "Net" p:arg => BitNetwork F (Fintype.card p)
variable (time : Fin (((events v.mesh).length + 1) *
      Fintype.card ((r : Public v.sampler h v.W k v.wideJobs) × Fin
        (HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
          v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) w r))) → Data)
    (vertex : CoreBoard.Site h (2^v.W) k) (j : Fin (events v.mesh).length)
    (control : ∀ a : SiteControls.Field v.widePacketDegree,
      controlAddress (v.wideDated h w ell unitCost)
        ((v.wideSpillDates h w ell unitCost bits first).spillControlWork
          (v.wideSpillRankEnd h w bits first)) j ((bs) vertex) a < G.u)
    (signedControl : ∀ a : SiteControls.Field v.widePacketDegree,
      controlAddress (v.wideDated h w ell unitCost)
        ((v.wideSpillDates h w ell unitCost bits first).roleRoot
          (v.wideSpillRankEnd h w bits first) 2) j ((bs) vertex) a < G.u)
    (mode : ballotAddress (v.wideDated h w ell unitCost)
      ((v.wideSpillDates h w ell unitCost bits first).roleRoot
        (v.wideSpillRankEnd h w bits first) 2) j ((bs) vertex) 0 < G.u)
    (tagSmall : v.signedTagCeiling ≤ G.W + 1)
    (laneSmall : v.wideNeighborDigits w unitCost ≤ G.W + 1)

local notation "s" => (bs) vertex
local notation "seatOf" => fun a : Fiber (attempts:=v.wideJobs) v.sampler ((bs).symm s)=>
  (finProdFinEquiv.symm (ports a.val)).2
local notation "feeRole" => fun (a : Fiber (attempts:=v.wideJobs) v.sampler ((bs).symm s)) b=>
    v.wide_shelf_role_fit h a.val b
local notation "raw" => LedgerStep.outerWord (Ex:=Ex) (Sel:=Sel) («degree»:=degree) («cap»:=cap) G es room ports time j s
local notation "sub" => LedgerStep.substepWord (Ex:=Ex) (Sel:=Sel) («degree»:=degree) («cap»:=cap) G es room ports time j s


open Tagged.PassiveWindow DatedSpillOffsets
variable (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : Data→Bool)
local notation "seen" => Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))

private theorem calendarFeedVertexValue {bdy} (feed : (events v.mesh).get j = .feed bdy) :
    TypedWiring.value (P:=V)
      (v.calendarRow h w ell unitCost bits datedROM datedWork terminalROM terminalWork first G time s j
        control signedControl mode tagSmall laneSmall) seen =
    TypedWiring.value (P:=V) (spillRow (F:=F) (slots:=seats) (e:=digits) G g cw j s control raw laneSmall
      v.sampler vertex (panel j).base (fun a side => v.wide_shelf_role_fit h a.val side)
      (DatedSpillOffsets.spillSeat v.sampler vertex)) seen := by
  let clipAt (loc : CoreBoard.Site h (2^v.W) k) (takeSeat : Fiber (attempts:=v.wideJobs) v.sampler loc → Fin degree) :=
    TypedWiring.value (P:=V)
      (spillRow (F:=F) (slots:=seats) (e:=digits) G g cw j s control raw laneSmall
        v.sampler loc (panel j).base (fun a side => v.wide_shelf_role_fit h a.val side) takeSeat) seen
  let physical (loc : CoreBoard.Site h (2^v.W) k) :=
    clipAt loc (fun a => (finProdFinEquiv.symm (ports a.val)).2)
  have nameEq := congrArg physical ((bs).symm_apply_apply vertex)
  have seatEq : (fun a : Fiber (attempts:=v.wideJobs) v.sampler vertex => (finProdFinEquiv.symm (ports a.val)).2) =
      DatedSpillOffsets.spillSeat v.sampler vertex := by
    funext a
    exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (name (site v.sampler a.val), ⟨HistoryRoles.code v.sampler a.val,code_bound v.sampler a.val⟩))
  exact (v.calendarRow_feed h w ell unitCost bits datedROM datedWork terminalROM terminalWork first G time s j
    control signedControl mode tagSmall laneSmall out ext sel data feed).trans (nameEq.trans (congrArg (clipAt vertex) seatEq))

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
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option cleanup.letToHave false

-- Read the paid calendarRow and all four datum assignments from the actual goal.
open Lean Meta in
private def feedVertexFromPhysical (target vertex observed : Lean.Expr) : MetaM Lean.Expr := do
  let spec ← getConstInfo ``calendarFeedVertexValue
  let expose (n : Name) (term : Lean.Expr) : MetaM Lean.Expr := do
    let term := term.consumeMData
    if term.isAppOf n then return term
    let some found ← whnfUntil term n | throwError "expected {n} in the physical selected feed row"
    return found
  let actualEq ← expose ``Eq target
  let feedEq ← expose ``Eq (← inferType observed)
  unless actualEq.isAppOfArity ``Eq 3 && feedEq.isAppOfArity ``Eq 3 do throwError "expected physical and witnessed feed equalities"
  let rawEvent := feedEq.getAppArgs[2]!.consumeMData
  unless rawEvent.isApp && rawEvent.getAppFn.constName!.toString.endsWith ".feed" do throwError "expected the witnessed feed boundary"
  forallTelescope spec.type fun binders conclusion => do
    let mut slots : Array (Option Lean.Expr) := Array.replicate binders.size none
    let align (a b : Lean.Expr) (xs : Array (Option Lean.Expr)) : MetaM (Array (Option Lean.Expr)) := do
      let key := a.getAppFn.constName!
      let trueTerm ← expose key b
      unless a.getAppNumArgs == trueTerm.getAppNumArgs do throwError "wrong physical arity for {key}"
      let mut result := xs
      for (formal,physicalArg) in a.getAppArgs.zip trueTerm.getAppArgs do
        if let some idx := binders.idxOf? formal.consumeMData then result := result.set! idx (some physicalArg)
      return result
    let sourceValue := conclusion.getAppArgs[1]!.consumeMData
    let physicalValue ← expose sourceValue.getAppFn.constName! actualEq.getAppArgs[1]!
    unless sourceValue.getAppNumArgs == 6 && physicalValue.getAppNumArgs == 6 do throwError "expected the six-operand network value"
    slots ← align sourceValue physicalValue slots
    slots ← align sourceValue.getAppArgs[4]! physicalValue.getAppArgs[4]! slots
    let mut current := sourceValue.getAppArgs[5]!.consumeMData
    let mut physicalPins := physicalValue.getAppArgs[5]!.consumeMData
    for _ in [:3] do
      unless current.isAppOfArity ``Sum.elim 5 do throwError "expected the prepared three-way pin assignment"
      physicalPins ← expose ``Sum.elim physicalPins
      slots ← align current physicalPins slots
      current := current.getAppArgs[4]!.consumeMData
      physicalPins := physicalPins.getAppArgs[4]!.consumeMData
    slots ← align current physicalPins slots
    for i in [:binders.size] do
      let label := (← binders[i]!.fvarId!.getDecl).userName.eraseMacroScopes
      if label == `vertex then slots := slots.set! i (some vertex)
      if label == `bdy then slots := slots.set! i (some rawEvent.appArg!)
      if label == `feed then slots := slots.set! i (some observed)
      unless slots[i]!.isSome do throwError "missing real theorem parameter {label} at {i}"
    return mkAppN (← mkConstWithFreshMVarLevels spec.name) (slots.map Option.get!)

open Lean Meta Elab Tactic in
local elab "takeFeedVertex " label:ident " at " vertex:ident " witnessingFeed " witness:ident : tactic => withMainContext do
  let currentGoal ← getMainGoal
  let proof ← feedVertexFromPhysical (← currentGoal.getType) (← getFVarFromUserName vertex.getId) (← getFVarFromUserName witness.getId)
  let (_, nextGoal) ← (← currentGoal.define label.getId (← inferType proof) proof).intro1P
  replaceMainGoal [nextGoal]

open Lean Meta Elab Tactic in
local elab "finishFeedReadAtGoal " "[" vertexEvidence:term ", " rankedEvidence:term ", " issuedOperation:term "]" : tactic =>
  withMainContext do
    let feedGoal ← getMainGoal
    let some (_, _, goalLast) := (← whnf (← feedGoal.getType)).eq?
      | throwError "expected an equality at the final site"
    let physicalInputs := goalLast.getAppArgs
    unless physicalInputs.size ≥ 3 do throwError "expected the site and two endpoint states on the right"
    let lastThree := physicalInputs.extract (physicalInputs.size - 3) physicalInputs.size
    let paidVertex ← instantiateMVars (← elabTerm vertexEvidence none)
    let paidRank ← instantiateMVars (← elabTerm rankedEvidence none)
    let paidOperator ← instantiateMVars (← elabTerm issuedOperation none)
    let paidVertexEq ← whnf (← inferType paidVertex)
    let paidRankEq ← whnf (← inferType paidRank)
    let some (vertexCarrier, vertexFrom, vertexTo) := paidVertexEq.eq?
      | throwErrorAt vertexEvidence "expected the physical vertex equality"
    let some (rankCarrier, rankFrom, rankTo) := paidRankEq.eq?
      | throwErrorAt rankedEvidence "expected the ranked carry equality"
    let paidLast := mkAppN paidOperator lastThree
    let rankedLast := mkAppN (mkConst ``Eq.trans paidRankEq.getAppFn.constLevels!)
      #[rankCarrier, rankFrom, rankTo, goalLast, paidRank, paidLast]
    let paidChain := mkAppN (mkConst ``Eq.trans paidVertexEq.getAppFn.constLevels!)
      #[vertexCarrier, vertexFrom, vertexTo, goalLast, paidVertex, rankedLast]
    feedGoal.assign paidChain
    replaceMainGoal []


-- Before the local protocol notation. This specialization uses one congrArg
-- on the complete function of row quantities, for either kind of premise.
private theorem physicalFeedBeforeOfFalse {α : Sort _} {flag : Bool}
    (off : flag = false) (corrected previous : α) (P : α → Prop)
    (before : P previous) : P (if flag then corrected else previous) := by
  have selected : (if flag then corrected else previous) = previous := by
    subst flag
    rfl
  exact Eq.mpr (congrArg P selected) before

open Lean Meta Elab Term in
local elab "feedBeforeOperand% " checkName:ident witness:term:max : term <= expected => do
  let off ← getFVarFromUserName checkName.getId
  let before ← elabTerm witness none
  -- These are the registered low/preEq domains after the caller has supplied
  -- its physical board, state, and date. Inspect only the outer proposition.
  let wanted := expected.consumeMData
  let isBound := wanted.isForall
  forallBoundedTelescope wanted (some (if isBound then 1 else 0)) fun rows pred => do
    let pred := pred.consumeMData
    unless (if isBound then pred.isAppOf ``LE.le || pred.isAppOf ``Nat.le
            else pred.isAppOfArity ``Eq 3) do
      throwError "expected the ranked predecessor bound or installed width equality"
    let operands := pred.getAppArgs
    let left := operands[operands.size - 2]!.consumeMData
    let .app entryPrefix last := left | throwError "expected an indexed amount or installed width"
    if isBound then
      unless last == rows[0]! do throwError "expected the authenticated physical row index"
    -- low has (selected row); preEq has (installedWidths ends selected).
    let selected := (if isBound then entryPrefix else last).consumeMData.headBeta.consumeMData
    unless selected.isAppOfArity ``ite 5 do throwError "expected the registered false selector"
    let #[carrier, test, _, yes, previous] := selected.getAppArgs | throwError "expected both dated quantities"
    let some (_,flag,trueVal) := test.consumeMData.eq? | throwError "expected a Bool flag test"
    unless trueVal.isConstOf ``Bool.true do throwError "expected attempt = true"
    let family ← withLocalDeclD `rowAmounts carrier fun amounts => do
      let entry := if isBound then mkApp amounts last else mkApp entryPrefix amounts
      let closedPred := mkAppN pred.getAppFn (operands.set! (operands.size - 2) entry)
      mkLambdaFVars #[amounts] (← mkForallFVars rows closedPred)
    return mkAppN (mkConst ``physicalFeedBeforeOfFalse selected.getAppFn.constLevels!)
      #[carrier, flag, off, yes, previous, family, before]


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
local notation "Buy" => PurchaseList (F:=F) («C»:=C) menu x source target count
local notation "Ex" => OpenPins h width (rout).catalyst
local notation "pathReportAt" π:arg j:arg => v.wide_reported_path h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
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
variable (height : v.BranchRoleHeight x.h x.w)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unit cpu.room).2
local notation "W" => Native.wordBits h d Native.copies
local notation "root" => (CalendarTape.Prefix.start : CalendarTape.Prefix sl es (base perm) es (base perm))
local notation "tree" => CalendarTape.Prefix.cursorSlot («slot»:=sl) (events:=es) (x₀:=base perm)
local notation "ws" => CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "top" => CalendarTape.Prefix.atCursor root
local notation "branch" => CalendarTape.Prefix.histories root path
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

local notation "data" ok:arg words:arg q:arg => v.calendarDayPins («C»:=C) m ell short u δ ξ x cpu support routeAge
  prices pricePos groupsFit metadata lanesFit buy e perm i tag height ok words q
local notation "scr" => v.wideInstalledLayout x m ell short u δ ξ unit g
local notation "first" => (scr).pruneScratch+(scr).pruneRows+1
local notation "rom" => v.wideInstalledRoot x
local notation "time" => SignedSites.calendarTime (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unit)
local notation "actualRow" s:arg j:arg => v.calendarRow h width ell unit v.maxBits rom S ((g).romEnd rom) ((g).workEnd S)
  first G time s j (control.spillRead s j) (control.signedRead s j) (control.mode s j) control.tag control.lane
local notation "step" => CalendarTape.Prefix.atStep ((Z).width perm) ((Z).operator perm)
local notation "matrixAt" j:arg => indexedStep tree ws step es top branch j
local notation "valAt" q:arg s:arg j:arg => datedState tree ws s es top branch j (q s)


local notation "sites₀" => siteLast h d k+1
local notation "graphSites" => siteNumber h d k
local notation "ends" => sorted v.sampler perm.symm v.depth (shape).mark ∘ (shape).order
local notation "stock₀" => v.fixedTerminalStock (v.widePlacement h width) h width
local notation "checkout" => v.wideSignedCheckoutAt h width S stock₀ v.radius perm.symm (wideRouteOrder h d k)
  (v.wideFundedRaw h width v.maxBits input)
local notation "B" => (b).coreMount perm.symm graphSites order checkout
local notation "atPrune" => (runAt).2.2.2.choose_spec.1.choose
local notation "body" j:arg => v.wideSpillPage h width v.maxBits first (j).val
local notation "goods" => commodityGraph perm.symm graphSites
local notation "qty" j:arg => fun commodity : Goods h v.W k => RouteSettlement.actual (body j).overflow atPrune (PurchaseInventory.slot commodity)
local notation "rawTip" t:arg => ws (boundaryState tree es top branch t)
local notation "ord" => ProtocolRAMDateSpillRank.spillEnum B (wideRouteOrder h d k)


open LinearAlgebra.SpectralBooks.SiteTensor Tagged.PassiveWindow
open HistoryRoles.Terminal WireTelescope.PassMatrix DateSpill
local notation "degs" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "maxDigit" => v.wideNeighborCap width unit
local notation "holder" => named v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order
local notation "socket" => shelfSlot («h»:=h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "correct" => v.wideSpillDates h width ell unit v.maxBits first

/-- Reindex a family of propositions along the physical enumeration of sites. -/
private theorem allFeedSites {α β : Type} (enumeration : α ≃ β) (predicate : β → Prop)
    (physical : ∀ vertex, predicate (enumeration vertex)) : ∀ s, predicate s :=
  enumeration.surjective.forall.mpr physical

-- Read the indexed proposition straight from the purchased-row goal. It includes
-- the entire memory state, so restating it would elaborate that state a second time.
open Lean Meta Elab Tactic in
local elab "indexFeedSites " enumeration:term : tactic => withMainContext do
  let destination ← getMainGoal
  let .forallE siteName siteType predicateBody siteBinder ← whnf (← destination.getType)
    | throwError "expected a family of site propositions"
  let predicate := Lean.Expr.lam siteName siteType predicateBody siteBinder
  let enumerator ← Term.elabTerm enumeration none
  let enumType ← whnf (← inferType enumerator)
  unless enumType.isAppOfArity ``Equiv 2 do throwError "expected the physical site equivalence"
  let bridge := mkAppN (mkConst ``allFeedSites) #[enumType.getAppArgs[0]!, siteType, enumerator, predicate]
  let .forallE _ physicalType _ _ ← whnf (← inferType bridge) | throwError "expected a physical site obligation"
  let physical ← mkFreshExprSyntheticOpaqueMVar physicalType
  destination.assign (mkApp bridge physical)
  replaceMainGoal [physical.mvarId!]

-- Eliminate a measured existential into the current proposition. The continuation
-- keeps the actual width and its two casts as variables in the rank proof.
open Lean Meta Elab Tactic in
local elab "feedWitness " witnessName:ident valueName:ident proofName:ident : tactic => withMainContext do
  let destination ← getMainGoal
  let evidence ← getFVarFromUserName witnessName.getId
  let claim ← whnf (← inferType evidence)
  unless claim.isAppOfArity ``Exists 2 do throwError "expected a measured width witness"
  let domain := claim.getAppArgs[0]!
  let predicate := claim.getAppArgs[1]!
  let result ← destination.getType
  let nextType := Lean.Expr.forallE valueName.getId domain
    (.forallE proofName.getId (mkApp predicate (.bvar 0)) result .default) .default
  let nextProof ← mkFreshExprSyntheticOpaqueMVar nextType
  let eliminator := mkConst ``Exists.elim claim.getAppFn.constLevels!
  destination.assign (mkAppN eliminator #[domain, predicate, result, evidence, nextProof])
  let (_, withValue) ← nextProof.mvarId!.intro1P
  let (_, withProof) ← withValue.intro1P
  replaceMainGoal [withProof]

-- Use after the site has been introduced, when its physical row equality is the goal.
open Lean Meta Elab Tactic in
local elab "takeFeedPins " dataName:ident recordName:ident : tactic => withMainContext do
  let headAt (name : Lean.Name) (e : Lean.Expr) : MetaM Lean.Expr := do
    let e := e.consumeMData
    if e.isAppOf name then return e
    let some exposed ← whnfUntil e name | throwError "expected {name} in the selected feed row"
    return exposed
  let branches (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
    let split ← headAt ``Sum.elim e
    unless split.isAppOfArity ``Sum.elim 5 do
      throwError "expected a pair of complete pin assignments"
    return split.getAppArgs
  let goal ← getMainGoal
  let equality ← headAt ``Eq (← goal.getType)
  unless equality.isAppOfArity ``Eq 3 do throwError "expected the site's physical row equality"
  let physical ← headAt ``ThreeFlat.Routing.TypedWiring.value equality.getAppArgs[1]!
  unless physical.getAppNumArgs == 6 do throwError "expected the evaluated network and its pins"
  let external ← branches physical.getAppArgs.back!
  let selected ← branches external[4]!
  let purchased ← branches selected[4]!
  -- @Sum.elim α β γ left right gives the function type α → γ for its left branch.
  let dataType ← mkArrow purchased[0]! purchased[2]!
  let recordType ← mkArrow selected[0]! selected[2]!
  let (_, afterData) ← (← goal.define dataName.getId dataType purchased[3]!).intro1P
  let (_, afterRecord) ← (← afterData.define recordName.getId recordType selected[3]!).intro1P
  replaceMainGoal [afterRecord]

private theorem feedReadFromFalse {pinFlag : Bool} (isFeed : pinFlag = false)
    (readFamily : (sideFlag : Bool) → sideFlag = false → Prop)
    (initialRead : readFamily false rfl) : readFamily pinFlag isFeed := by
  subst pinFlag
  exact initialRead

open Lean Meta Elab Tactic in
local elab "liftIndexedFeedRead " eqName:ident " using " readExpr:term : tactic => withMainContext do
  let goal ← getMainGoal
  let readTarget ← instantiateMVars (← goal.getType)
  let ack ← getFVarFromUserName eqName.getId
  let eqTy ← inferType ack
  let off := mkConst ``Bool.false
  unless eqTy.isAppOfArity ``Eq 3 && eqTy.getAppArgs[0]!.isConstOf ``Bool && eqTy.getAppArgs[2]! == off do
    throwError "expected the selected physical flag to equal false"
  let flag := eqTy.getAppArgs[1]!
  let normalized ← Lean.Core.transform readTarget (post := fun t => do
    let .app f pos := t | return .done t
    let .lam _ _ branchBody _ := f.consumeMData | return .done t
    let branchBody := branchBody.consumeMData
    unless branchBody.isAppOfArity ``ite 5 do return .done t
    let test := branchBody.getAppArgs[1]!.consumeMData
    unless test.isAppOfArity ``Eq 3 do return .done t
    let args := test.getAppArgs
    unless args[0]!.isConstOf ``Bool && args[2]!.isConstOf ``Bool.true &&
        (args[1]!.instantiate1 pos).consumeMData == flag do return .done t
    return .done (branchBody.instantiate1 pos))
  let family ← withLocalDeclNoLocalInstanceUpdate `sideFlag .default (mkConst ``Bool) fun side => do
    withLocalDeclNoLocalInstanceUpdate `sideIsFeed .default (← mkEq side off) fun sideEq => do
      let general := normalized.replace fun t =>
        if t == ack then some sideEq else if t == flag then some side else none
      mkLambdaFVars #[side, sideEq] general
  let initialRead ← Term.withSynthesize (postpone := .no) <| Tactic.elabTerm readExpr none
  goal.assign (mkAppN (mkConst ``feedReadFromFalse) #[flag, ack, family, initialRead])
  replaceMainGoal []

open Lean Meta Elab Term in
local elab "outerFeedRead% " saved:ident date:ident site:ident right:term:max amount:ident : term => do
  let dataArg ← getFVarFromUserName saved.getId
  let some savedVal := (← dataArg.fvarId!.getDecl).value?
    | throwError "expected a let alias for the purchased pin assignment"
  let pinValue := savedVal.consumeMData
  let pinApplication ← if pinValue.isAppOf ``calendarDayPins then pure pinValue else do
    let some exposed ← whnfUntil pinValue ``calendarDayPins
      | throwError "expected the original calendarDayPins assignment"
    pure exposed
  -- The first 37 arguments of the read are the published pin assignment's
  -- 34 path parameters followed by its kept witness, entry words and states.
  let inputs := pinApplication.getAppArgs
  unless inputs.size == 37 do throwError "expected the selected path and its three purchased operands"
  let atDate ← getFVarFromUserName date.getId
  let atSite ← getFVarFromUserName site.getId
  let direction ← Term.elabTerm right (some (mkConst ``Bool))
  let widthProof ← getFVarFromUserName amount.getId
  let widthType := (← inferType widthProof).consumeMData
  let eqn ← if widthType.isAppOf ``Eq then pure widthType else do
    let some exposed ← whnfUntil widthType ``Eq | throwError "expected the measured width equality"
    pure exposed
  unless eqn.isAppOfArity ``Eq 3 do throwError "expected the target widths in a complete equality"
  let thm ← mkConstWithFreshMVarLevels ``wide_calendar_day_outer_rebased_bits
  return mkAppN thm (inputs ++
    #[atDate, atSite, direction, eqn.getAppArgs[2]!, widthProof])


set_option maxHeartbeats 20000000 in
/-- Every actual feed circuit on the accepted path evaluates to its original
operator on the two adjacent dated states. -/
theorem calendar_feed_day (j : Fin (es).length) (bdy : Boundary) (on : (es).get j=.feed bdy) :
    v.calendarDayRead («C»:=C) m ell short u δ ξ x cpu room control support routeAge prices pricePos groupsFit
      metadata lanesFit buy e perm i tag height j := by
  apply (v.calendarDayRead_iff («C»:=C) m ell short u δ ξ x cpu room control support routeAge prices pricePos
    groupsFit metadata lanesFit buy e perm i tag height j).2
  have measured := v.wide_calendar_day_feed_scalar m ell short u δ ξ x cpu support routeAge
    prices pricePos groupsFit metadata lanesFit buy e perm i tag height j bdy on
  feedWitness measured rest measuredFits
  feedWitness measuredFits pre measuredLast
  feedWitness measuredLast post operator
  have no : (correct).attempt j=false := by
    change (match (es).get j with | .attempt _=>true | .feed _=>false)=_
    rw [on]
  have bound (t : Fin ((es).length+1)) (r : Fin (shape).count) : (shape).bits t r ≤ maxDigit :=
    ((shape).fits t r false).trans (v.wide_outer_lane h width unit (holder (r,false)))
  intro ok word q
  indexFeedSites (graphSites)
  intro vertex
  takeFeedPins savedData savedRecord
  let s:=graphSites vertex
  let spill:=qty j
  let active (side : Bool) := cond side ((B).actual.chordWidths (routeLoad (B).ordinary spill)) ((goods).chordWidths spill)
  let val₀:=cast (congrArg (fun T=>State T s) (((shape).atWidth j.castSucc).symm.trans pre)) (valAt q s j.castSucc)
  let val₁:=cast (congrArg (fun T=>State T s) (((shape).atWidth j.succ).symm.trans post)) (valAt q s j.succ)
  let endpoint (side : Bool) : State (rest+active side) s :=
    Bool.rec (motive:=fun side=>State (rest+active side) s) val₀ val₁ side
  let taps := LedgerStep.outerWord («Ex» := Ex) («Sel» := Fin (CalendarTape.bits sl es))
    («D» := D) (cap := maxDigit) G es roles socket time j s
  have run:=v.wide_ranked_spill_carry («X» := Ex) («Y» := Fin (CalendarTape.bits sl es)) («Z» := D) m ell short u δ ξ unit x cpu v.calendarUnit_rate support prices pricePos
    buy groupsFit metadata lanesFit e perm tag path height j (G) rfl vertex rest endpoint
    (feedBeforeOperand% no (bound j.castSucc)) (bound j.succ)
    (feedBeforeOperand% no pre) post taps (control.spillRead s j)
    (fun t c=>SignedSites.calendar_spill_shelf v m ell short unit cpu j s t (TurnShelf.projection c).1)
    control.lane (fun _=>rfl) e savedRecord savedData (by
      intro side
      cases side
      · liftIndexedFeedRead no using
          (outerFeedRead% savedData j s false pre)
      · exact (outerFeedRead% savedData j s true post))
  takeFeedVertex savedVertex at vertex witnessingFeed on
  finishFeedReadAtGoal [savedVertex, run, operator]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

-- Skip premise scoring for this large declaration during this module’s export.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun names => "calendar_feed_day" :: names

end OAI
