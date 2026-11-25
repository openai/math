import OAI.Hierarchy.TaggedWideCalendarTerminalPins
import OAI.Hierarchy.TaggedWidePathRoleCells
import OAI.Hierarchy.TaggedWideBranchRoleHeight
import OAI.Hierarchy.TaggedWideOriginalCalendarPrice
import OAI.Hierarchy.WidthSelectedSpillRegisters
import OAI.Hierarchy.ProbeFixedFundedCalendarFeed

namespace OAI
/-! # The chosen original feed, measured scheduled sheets and authenticated native debit -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets WireTelescope Tagged CalendarTape
open CoreBoard.PhysicalTerm Filter
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 350000
set_option Elab.async false
set_option cleanup.letToHave false
attribute [local irreducible] Nat.pow

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width size : ℕ)
    (π : Equiv.Perm (Tagged.Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
    (expanse : v.wideFundedSize h width v.maxBits ≤ size) (late : v.reportHeight ≤ h)
    (room : v.ReportWordRoom h width)
local notation "reader" => v.wideSelector h width age budget small
local notation "slots" => (reader).format.slot
local notation "es" => events v.mesh
local notation "start" => v.wideOrigin h width size seed π
local notation "table" => v.widePlacement h width
local notation "ceiling" => (v.privateArena table h width).endAddress v.mesh
local notation "stock" => v.fixedTerminalStock table h width
local notation "w" => Native.wordBits h (2^v.W) Native.copies
variable (j : Path slots es start)
local notation "raw" => (reader).format.windows.header es (encode slots es start j) seed
local notation "tape" => v.wideFundedRaw h width v.maxBits raw
local notation "checkout" => v.wideSignedCheckoutAt h width size stock v.radius π.symm
  (wideRouteOrder h (2^v.W) k) tape
local notation "pathReport" => v.wide_reported_path h width size π seed age budget small expanse late room j


open ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
local notation "wire" => WireTelescope.CalendarTape.Prefix.atWidth («slot»:=slots) (events:=es) (x₀:=start) (S:=siteLast h (2^v.W) k+1) (fun {_ _} path => v.wideCursorWidth h width size π seed age budget small path)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans expanse
local notation "cap" c:arg => HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh c v.keepLimit (CatalystArchive.fuel v.mesh) width
variable (unitCost:ℕ)
    (replay:v.cursorReplayHeight≤h) (measure:v.wideDatedLedgerHeight≤h)
    (bounded : ∀(perm:Equiv.Perm (Fin (2^h))) (mem:Boot.Tape h (2^v.W)),
      let o:=wideRouteOrder h (2^v.W) k
      let m:=v.wideSignedMidAt h width size stock v.radius perm o mem
      let c:=v.wideSignedCheckoutAt h width size stock v.radius perm o mem
      c ceiling=0→v.DatedWireFits h width perm m c unitCost)

attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit

/- Recover the dates from the reconciliation's actual count of issued records. -/
open Lean Elab Term in
local elab "selectedPathDates " cert:ident : term => do
  let receipt ← Meta.getFVarFromUserName cert.getId
  let reconciliation ← Meta.whnf (← Meta.inferType receipt)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected a settlement reconciliation"
  let some rowCountExpr := reconciliation.getAppArgs[7]? | throwError "expected a reconciliation record count"
  let count ← Meta.whnf rowCountExpr
  unless count.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the native record count"
  let issuedExpr ← Meta.whnf count.getAppArgs.back!
  unless issuedExpr.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the dated issues"
  return ← instantiateMVars issuedExpr.getAppArgs.back!



open ThreeFlat.RAM ChordGraph
open CoreBoard.HistoryRoles.RoleProgram
variable (routeAge : v.routingHeight ≤ h) (floor : v.widthFloor ≤ width)
local notation "shape" => v.widePathRoles h width size π seed age budget small expanse late room j unitCost replay measure bounded
local notation "cal" => v.routedSchedule h width size arenaRoom seed age budget small expanse routeAge floor room
local notation "rootCursor" => (CalendarTape.Prefix.start : CalendarTape.Prefix slots es start es start)
local notation "tree" => CalendarTape.Prefix.cursorSlot («slot»:=slots) (events:=es) (x₀:=start)
local notation "ws" => CalendarTape.Prefix.atWidth ((cal).width π)
local notation "steps" => CalendarTape.Prefix.atStep ((cal).width π) ((cal).operator π)
local notation "originCursor" => CalendarTape.Prefix.atCursor rootCursor
local notation "route" => CalendarTape.Prefix.histories rootCursor j
local notation "matrixAt" t:arg => indexedStep tree ws steps es originCursor route t
local notation "rawTip" t:arg => ws (boundaryState tree es originCursor route t)
local notation "graphSites" => siteNumber h (2^v.W) k
local notation "B" => (table).catalogue.coreMount π.symm graphSites (v.wideOrder h width) checkout
local notation "ord" => ProtocolRAMDateSpillRank.spillEnum B (wideRouteOrder h (2^v.W) k)
local notation "goods" => commodityGraph π.symm graphSites
local notation "ends" => HistoryRoles.sorted v.sampler π.symm v.depth (shape).mark ∘ (shape).order
local notation "rowAge" => (max_le_iff.mp routeAge).1
local notation "sub" => (max_le_iff.mp ((max_le_iff.mp rowAge).2)).2
local notation "graphs" => (max_le_iff.mp sub).2
local notation "feedHeight" => (max_le_iff.mp ((max_le_iff.mp graphs).2)).1
local notation "sites₀" => siteLast h (2^v.W) k+1
variable (first : ℕ) (image : Memory w)
local notation "qty" t:arg => fun i : Goods h v.W k => RouteSettlement.actual (v.wideSpillPage h width v.maxBits first (t).val).overflow image (PurchaseInventory.slot i)
variable (stored : ∀ a < (v.privateArena table h width).endAddress v.mesh, image a = checkout a)
attribute [local irreducible] widePathRoles CatalystArchive.fuel LinearAlgebra.SpectralBooks.PortGraph.chordWidths

/- Use the concrete occurrence count and issued row names carried by the reconciliation. -/
open Lean Elab Term in
local elab "datedFeedResult " mode:ident : term => do
  let getVar : Lean.Name → TermElabM Lean.Expr := fun n => do return ← Meta.getFVarFromUserName n
  let fmt ← getVar `v
  let ty := (← Meta.inferType fmt).consumeMData
  let formatArgs := ty.getAppArgs
  unless formatArgs.size == 8 do throwError "unexpected fixed protocol format arguments {formatArgs.size}"
  let reconciliation ← getVar `reconciliation
  let receiptType ← Meta.whnf (← Meta.inferType reconciliation)
  unless receiptType.isAppOf ``Whole.Reconciliation do throwError "expected a dated reconciliation"
  let receiptArgs := receiptType.getAppArgs
  let alignment := mkAppN (← getVar `aligned) #[receiptArgs[7]!, receiptArgs[12]!, receiptArgs[13]!]
  let initial ← #[`v,`h,`width,`size,`inverseRows,`inputWord,`expanse,`paidAge,`budget,`small,`pricesAt,
    `dates,`pos,`measure,`priceHeight,`reconciliation].mapM getVar
  let finish ← #[`first,`tick,`bdy,`on,`image,`scalar,`stored].mapM getVar
  let arguments := formatArgs ++ initial ++ #[alignment] ++ finish
  if mode.getId == `widths then
    return mkAppN (← Meta.mkConstWithFreshMVarLevels ``wide_spill_feed_shapes_at) arguments
  else
    let chosen ← getVar `chosen
    let gateType := (← instantiateMVars (← Meta.inferType chosen)).consumeMData
    unless gateType.isAppOf ``wireFeedPresentation do throwError "expected a presentation of the elected feed, got {gateType.getAppFn} with {gateType.getAppNumArgs} arguments"
    let gateArgs := gateType.getAppArgs
    return mkAppN (← Meta.mkConstWithFreshMVarLevels ``wide_calendar_feed_at)
      (arguments ++ gateArgs.extract (gateArgs.size-3) gateArgs.size ++ #[chosen])

private theorem funded_path_feed_shapes {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width size : ℕ)
    (π : Equiv.Perm (Tagged.Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
    (expanse : v.wideFundedSize h width v.maxBits ≤ size) (late : v.reportHeight ≤ h)
    (room : v.ReportWordRoom h width)
    (j : Path slots es start)
    (unitCost:ℕ)
    (replay:v.cursorReplayHeight≤h) (measure:v.wideDatedLedgerHeight≤h)
    (bounded : ∀(perm:Equiv.Perm (Fin (2^h))) (mem:Boot.Tape h (2^v.W)),
      let o:=wideRouteOrder h (2^v.W) k
      let m:=v.wideSignedMidAt h width size stock v.radius perm o mem
      let c:=v.wideSignedCheckoutAt h width size stock v.radius perm o mem
      c ceiling=0→v.DatedWireFits h width perm m c unitCost)
    (routeAge : v.routingHeight ≤ h) (floor : v.widthFloor ≤ width)
    (first : ℕ) (image : Memory w)
    (stored : ∀ a < (v.privateArena table h width).endAddress v.mesh, image a = checkout a)
    (tick : Fin (es).length) (bdy : Boundary) (on : (es).get tick=.feed bdy) :
    let spill:=qty tick
    ∃rest : Widths sites₀,
      installedWidths ends ((shape).bits tick.castSucc)=rest+(goods).chordWidths spill ∧
      installedWidths ends ((shape).bits tick.succ)=rest+(B).actual.chordWidths (routeLoad (B).ordinary spill) ∧
      ∀(s : Fin sites₀) (old : State (rawTip tick.castSucc) s) (new : State (rawTip tick.succ) s)
        (before : State (rest+(goods).chordWidths spill) s)
        (after₁ : State (rest+(B).actual.chordWidths (routeLoad (B).ordinary spill)) s),
        HEq old before→HEq new after₁→
          LedgerStep.carry ((B).onlySpill (F:=F) (graphSites).injective (publicChord h (2^v.W) k) spill ord)
            rest s before after₁=(matrixAt tick) s old new := by
  intro spill
  let evidence := v.wide_reported_path_funded_rows h width size π seed age budget small expanse late room j
  let paidAge := Classical.choose evidence
  let pricesAt := Classical.choose evidence.choose_spec
  let aligned {entries : ℕ} (ns : Fin entries → Fin (Fintype.card (Columns h (2^v.W)) * k)) (fees : Fin entries → ℕ) :=
    (Classical.choose evidence.choose_spec.choose_spec) ns fees
  let run := v.wide_funded_run_at h width v.radius π.symm raw v.maxBits size expanse paidAge budget small (0 : Word w)
  let receipt := Classical.choose_spec run
  let reconciliation := receipt.1
  let dates := selectedPathDates reconciliation
  have pos : 0 < Fintype.card (Columns h (2^v.W)) * k := Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨.inl ⟨0,Nat.two_pow_pos _⟩⟩) v.positive
  let area := v.privateArena table h width
  have scalar : PurchaseInventory.footprint h (Stages h (2^v.W)) k ≤ 2^w := by
    have slotsRoom := v.feed_room table h width
    have occurs : Event.feed bdy ∈ events v.mesh := (congrArg (fun e => e ∈ events v.mesh) on).mp ((events v.mesh).get_mem tick)
    have dated := area.within v.mesh (.feed bdy) occurs
    have words := (v.wide_stock_sizes h width ((le_max_right ..).trans paidAge) budget small).words.addresses
    change area.endAddress v.mesh < 2^w at words
    change 2*PurchaseInventory.footprint h (Stages h (2^v.W)) k ≤ area.stride at slotsRoom
    omega
  let inverseRows := π.symm
  let inputWord := raw
  let priceHeight : v.feedOperatorHeight ≤ h := feedHeight
  have measured := datedFeedResult widths
  have chosen := v.wide_routed_feed_on_path h width size arenaRoom π seed age budget small expanse routeAge floor room j tick on
  have actual := datedFeedResult scalarEntry
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let measured ← Lean.Meta.getFVarFromUserName `measured
    let value ← Lean.Meta.getFVarFromUserName `actual
    let measuredType ← Lean.Meta.whnf (← Lean.instantiateMVars (← Lean.Meta.inferType measured))
    let #[inputEquation, outputEquation] := measuredType.getAppArgs | throwError "expected two measured width equations"
    let #[_, _, inputWidth] := inputEquation.getAppArgs | throwError "expected the measured input width"
    let widthArgs := inputWidth.getAppArgs
    unless widthArgs.size ≥ 2 do throwError "expected a sum of retained and spill widths"
    let retainedWidth := widthArgs[widthArgs.size-2]!
    let target ← Lean.Meta.whnf (← Lean.instantiateMVars (← goal.getType))
    let #[domain,motive] := target.getAppArgs | throwError "expected a retained-width witness"
    let pair ← Lean.Meta.whnf (motive.beta #[retainedWidth])
    let #[front,rest] := pair.getAppArgs | throwError "expected the input width and remaining claims"
    let backAndAction ← Lean.Meta.whnf rest
    let #[back,action] := backAndAction.getAppArgs | throwError "expected the output width and scalar action"
    let left := Lean.mkAppN (Lean.mkConst ``And.left) #[inputEquation,outputEquation,measured]
    let right := Lean.mkAppN (Lean.mkConst ``And.right) #[inputEquation,outputEquation,measured]
    let tail := Lean.mkAppN (Lean.mkConst ``And.intro) #[back,action,right,value]
    let result := Lean.mkAppN (Lean.mkConst ``And.intro) #[front,rest,left,tail]
    goal.assign (Lean.mkAppN (Lean.mkConst ``Exists.intro target.getAppFn.constLevels!) #[domain,motive,retainedWidth,result])
    Lean.Elab.Tactic.replaceMainGoal []

private theorem funded_path_feed_scalar {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width size : ℕ)
    (π : Equiv.Perm (Tagged.Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
    (expanse : v.wideFundedSize h width v.maxBits ≤ size) (late : v.reportHeight ≤ h)
    (room : v.ReportWordRoom h width)
    (j : Path slots es start)
    (unitCost:ℕ)
    (replay:v.cursorReplayHeight≤h) (measure:v.wideDatedLedgerHeight≤h)
    (bounded : ∀(perm:Equiv.Perm (Fin (2^h))) (mem:Boot.Tape h (2^v.W)),
      let o:=wideRouteOrder h (2^v.W) k
      let m:=v.wideSignedMidAt h width size stock v.radius perm o mem
      let c:=v.wideSignedCheckoutAt h width size stock v.radius perm o mem
      c ceiling=0→v.DatedWireFits h width perm m c unitCost)
    (routeAge : v.routingHeight ≤ h) (floor : v.widthFloor ≤ width)
    (first : ℕ) (image : Memory w)
    (stored : ∀ a < (v.privateArena table h width).endAddress v.mesh, image a = checkout a)
    (tick : Fin (es).length) (bdy : Boundary) (on : (es).get tick=.feed bdy) :
    let spill:=qty tick
    ∃(rest : Widths sites₀)
      (before : installedWidths ends ((shape).bits tick.castSucc)=rest+(goods).chordWidths spill)
      (after₁ : installedWidths ends ((shape).bits tick.succ)=rest+(B).actual.chordWidths (routeLoad (B).ordinary spill)),
      ∀(s : Fin sites₀) (old : State (rawTip tick.castSucc) s) (new : State (rawTip tick.succ) s),
        LedgerStep.carry ((B).onlySpill (F:=F) (graphSites).injective (publicChord h (2^v.W) k) spill ord)
          rest s (cast (congrArg (fun T=>State T s) (((shape).atWidth tick.castSucc).symm.trans before)) old)
            (cast (congrArg (fun T=>State T s) (((shape).atWidth tick.succ).symm.trans after₁)) new)=
              (matrixAt tick) s old new := by
  intro spill
  have selectedShapes := funded_path_feed_shapes v h width size π seed age budget small expanse late room j
    unitCost replay measure bounded routeAge floor first image stored tick bdy on
  rcases selectedShapes with ⟨rest,oldWidths,newWidths,entries⟩
  exact ⟨rest,oldWidths,newWidths,fun s old new => entries s old new _ _ (cast_heq ..).symm (cast_heq ..).symm⟩

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
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x)
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

-- The observed protocol signature fixes the implicit parameters of the paid archive.
open Lean Elab Term in
local elab "selectedFeedArchive% " which:ident "[" supplied:term:max,* "]" : term => do
  let format ← Meta.getFVarFromUserName `v
  let parameters := (← Meta.inferType format).consumeMData.getAppArgs
  unless parameters.size == 8 do throwError "unexpected fixed-protocol signature"
  let mut xs := parameters
  for arg in supplied.getElems do
    xs := xs.push (← instantiateMVars (← elabTerm arg none))
  unless xs.size == 35 do throwError "unexpected selected-archive arity {xs.size}"
  let name := if which.getId == `registers then ``wide_selected_spill_registers else ``wide_selected_local_return
  return mkAppN (← Meta.mkConstWithFreshMVarLevels name) xs

local notation "runAt" => selectedFeedArchive% returned [κ,A,v,m,ell,short,u,δ,ξ,unit,N,x,cpu,v.calendarUnit_rate,
  support,prices,C,pricePos,buy,groupsFit,metadata,lanesFit,(rout).catalyst,e,perm,tag,path]
local notation "physicalRegister" => selectedFeedArchive% registers [κ,A,v,m,ell,short,u,δ,ξ,unit,N,x,cpu,v.calendarUnit_rate,
  support,prices,C,pricePos,buy,groupsFit,metadata,lanesFit,(rout).catalyst,e,perm,tag,path]
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

local notation "scr" => v.wideInstalledLayout x m ell short u δ ξ unit g
local notation "first" => (scr).pruneScratch+(scr).pruneRows+1
local notation "rom" => v.wideInstalledRoot x
local notation "time" => SignedSites.calendarTime (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unit)
local notation "step" => CalendarTape.Prefix.atStep ((Z).width perm) ((Z).operator perm)
local notation "matrixAt" j:arg => indexedStep tree ws step es top branch j
local notation "valAt" q:arg s:arg j:arg => datedState tree ws s es top branch j (q s)


local notation "rowAge" => (max_le_iff.mp routeAge).1
local notation "sub" => (max_le_iff.mp ((max_le_iff.mp rowAge).2)).2
local notation "graphs" => (max_le_iff.mp sub).2
local notation "feedHeight" => (max_le_iff.mp ((max_le_iff.mp graphs).2)).1


local notation "sites₀" => siteLast h d k+1
local notation "graphSites" => siteNumber h d k
local notation "ends" => sorted v.sampler perm.symm v.depth (shape).mark ∘ (shape).order
local notation "stock₀" => v.fixedTerminalStock (v.widePlacement h width) h width
local notation "checkout" => v.wideSignedCheckoutAt h width S stock₀ v.radius perm.symm (wideRouteOrder h d k)
  (v.wideFundedRaw h width v.maxBits input)
local notation "B" => (b).coreMount perm.symm graphSites order checkout
-- The initial memory and its storage equality come from one selected register record.
open Lean Meta Elab Term in
local elab "registeredFeedCell% " which:ident file:term:max : term => do
  let selected ← elabTerm file none
  if which.getId == `stored then
    let some storage := (← getEnv).getProjectionFnInfo? ``NativeSpillRegisters.Evidence.stored
      | throwError "expected the selected storage projection"
    return .proj ``NativeSpillRegisters.Evidence storage.i selected
  let some evidenceTy ← whnfUntil (← inferType selected) ``NativeSpillRegisters.Evidence
    | throwError "expected the purchased spill registers"
  let some expanded ← unfoldDefinition? evidenceTy.getAppArgs.back! true
    | throwError "expected the selected register specification"
  let spec := expanded.headBeta
  unless spec.getAppNumArgs == 39 && spec.getAppFn.constName?.any (fun n => n.getString! == "nativeRegisterFieldTypes") do
    throwError "unexpected physical register inputs"
  return spec.getAppArgs[34]!

local notation "atPrune" => (runAt).2.2.2.choose_spec.1.choose
local notation "body" j:arg => v.wideSpillPage h width v.maxBits first (j).val
local notation "goods" => commodityGraph perm.symm graphSites
local notation "qty" j:arg => fun commodity : Goods h v.W k=>RouteSettlement.actual (body j).overflow atPrune (PurchaseInventory.slot commodity)
local notation "rawTip" t:arg => ws (boundaryState tree es top branch t)
local notation "ord" => ProtocolRAMDateSpillRank.spillEnum B (wideRouteOrder h d k)


open Lean Elab Tactic Term in
local elab "applyFundedFeed " mode:ident terms:term:max,* : tactic => withMainContext do
  let goal ← getMainGoal
  let fmt ← Meta.getFVarFromUserName `v
  let parameters := (← Meta.inferType fmt).consumeMData.getAppArgs
  unless parameters.size == 8 do throwError "expected the parameters of the original protocol format"
  let mut arguments := parameters
  for stx in terms.getElems do
    arguments := arguments.push (← instantiateMVars (← Term.elabTerm stx none))
  let name := if mode.getId == `scalar then ``funded_path_feed_scalar else ``funded_path_feed_shapes
  let decl ← Meta.mkConstWithFreshMVarLevels name
  goal.assign (mkAppN decl arguments)
  replaceMainGoal []

/-- The exact widths at the two public ends of an elected feed, and the true
signed local operator on the same path. All released amounts come from the
sparse registers of the selected accepted post-pruning execution. -/
theorem wide_calendar_day_feed_shapes {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x)
    (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤x.h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight x.h x.w)
    (j : Fin (es).length) (bdy : Boundary) (on : (es).get j=.feed bdy) :
    let spill:=qty j
    ∃rest : Widths sites₀,
      installedWidths ends ((shape).bits j.castSucc)=rest+(goods).chordWidths spill ∧
      installedWidths ends ((shape).bits j.succ)=rest+(B).actual.chordWidths (routeLoad (B).ordinary spill) ∧
      ∀(s : Fin sites₀) (old : State (rawTip j.castSucc) s) (new : State (rawTip j.succ) s)
        (before : State (rest+(goods).chordWidths spill) s)
        (after₁ : State (rest+(B).actual.chordWidths (routeLoad (B).ordinary spill)) s),
        HEq old before→HEq new after₁→
          LedgerStep.carry ((B).onlySpill (F:=F) (graphSites).injective (publicChord h d k) spill ord)
            rest s before after₁=(matrixAt j) s old new := by
  applyFundedFeed shapes v, h, width, S, perm, seed, cpu.age, cpu.ready.credit, cpu.ready.size_le, Sfit,
    height.report, height.wordRoom, path, unit, height.replay, height.measure,
    (height.funded_aperture S unit Sfit v.calendarUnit_rate), routeAge, support.size.widthFloor, first,
    (registeredFeedCell% initial (physicalRegister)), (registeredFeedCell% stored (physicalRegister)), j, bdy, on


/-- Both states of the feed are cast directly by the measured equality on the
same path, giving the original scalar on every input pair. -/
theorem wide_calendar_day_feed_scalar {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x)
    (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤x.h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight x.h x.w)
    (j : Fin (es).length) (bdy : Boundary) (on : (es).get j=.feed bdy) :
    let spill:=qty j
    ∃(rest : Widths sites₀)
      (before : installedWidths ends ((shape).bits j.castSucc)=rest+(goods).chordWidths spill)
      (after₁ : installedWidths ends ((shape).bits j.succ)=rest+(B).actual.chordWidths (routeLoad (B).ordinary spill)),
      ∀(s : Fin sites₀) (old : State (rawTip j.castSucc) s) (new : State (rawTip j.succ) s),
        LedgerStep.carry ((B).onlySpill (F:=F) (graphSites).injective (publicChord h d k) spill ord)
          rest s (cast (congrArg (fun T=>State T s) (((shape).atWidth j.castSucc).symm.trans before)) old)
            (cast (congrArg (fun T=>State T s) (((shape).atWidth j.succ).symm.trans after₁)) new)=
              (matrixAt j) s old new := by
  applyFundedFeed scalar v, h, width, S, perm, seed, cpu.age, cpu.ready.credit, cpu.ready.size_le, Sfit,
    height.report, height.wordRoom, path, unit, height.replay, height.measure,
    (height.funded_aperture S unit Sfit v.calendarUnit_rate), routeAge, support.size.widthFloor, first,
    (registeredFeedCell% initial (physicalRegister)), (registeredFeedCell% stored (physicalRegister)), j, bdy, on

-- These two statements repeat the expanded source and target physical states.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_calendar_day_feed_shapes"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_calendar_day_feed_scalar"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
