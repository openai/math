import OAI.Hierarchy.TaggedWideCalendarEndpointFields
import OAI.Hierarchy.TaggedWideCalendarTerminalRoom
import OAI.Hierarchy.TaggedWideFundedSelectedShelf
import OAI.Hierarchy.TaggedWideSourceAlignmentUnique
import OAI.Hierarchy.TaggedWideCursorTerminalReport
import OAI.Hierarchy.TaggedWideCalendarShelfRows
import OAI.Hierarchy.TaggedWireActualRoutedSchedule

namespace OAI
/-! # The selected calendar's terminal shelf equation on its actual returned memory -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
set_option quotPrecheck false
set_option hygiene false
section SelectedShelfSockets

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows CatalystArchive
open Tagged Tagged.WideStack TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMEmit
open ProtocolRAMReportedPorts PurchaseFrozen
open scoped Classical BigOperators
open private fundedCutMarksAt from OAI.Hierarchy.TaggedWideFundedReceiptCore

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (tapeSize : ℕ)
    (π : Equiv.Perm (Fin (2^x.h))) (input : Boot.Tape x.h (2^v.W)) (unitCost : ℕ)

local notation "socketBoard" => (v.widePlacement x.h x.w).catalogue
local notation "socketOrder" => v.wideOrder x.h x.w
local notation "socketDir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "socketMarks" => fundedCutMarksAt v x.h x.w tapeSize π input
local notation "socketBought" => v.wideBoughtOrdinal x.h x.w π socketMarks

variable (raw : Fin (socketBoard).rows → ProtocolRAMEmit.Row)
    (geometry : Geometry (boardLayout x.h (2^v.W) k x.w (fuel v.mesh*x.w)) v.radius 1 raw)
    (actual : v.FundedCutRows x.h x.w tapeSize π input raw geometry unitCost)

local notation "socketPort" => FundedCutRows.port v x tapeSize π input unitCost raw geometry actual
local notation "socketAlignment" =>
  Alignment socketBoard v.sampler π v.depth socketMarks v.radius raw (fun i => (raw i).width)
    ((socketBoard).original v.sampler π v.depth socketMarks socketOrder socketBought)
local notation "socketLines" =>
  atScale ((socketBoard).transport socketOrder) (fun _ => v.W) v.W raw
local notation "socketInstalled" aligned:arg exclusiveProof:arg =>
  (CatalogueRows.Alignment.location v.sampler π v.depth socketMarks exclusiveProof socketBoard
    socketOrder socketBought raw aligned (fun _ => v.W) v.W x.w x.formats.2.1).trans (ReportSockets.packed socketDir)

/-- The installed shelf uses the purchased socket group and port at every positive native row. -/
theorem FundedCutRows.selected_shelf_sockets
    (issuer : socketAlignment) (sameNames : actual.sourceAlignment = issuer)
    (exclusiveProof : Exclusive socketMarks) :
    ∀ (j : {i : Fin (socketBoard).rows // 0 < pieces socketLines x.w i}) (side : Bool),
      (((socketInstalled issuer exclusiveProof) (j, side)).1.val = (raw j.val).group) ∧
      (((socketInstalled issuer exclusiveProof) (j, side)).2 = socketPort side j.val) := by
  cases sameNames
  apply CatalogueRows.Alignment.shelf_stage_anchor v.sampler π v.depth socketMarks exclusiveProof
    socketBoard socketOrder socketBought raw actual.sourceAlignment x.w x.formats.2.1
    socketDir socketPort v.W
  intro j side
  have atSocket := DFunLike.congr_fun (actual.aperture_eq exclusiveProof x.formats.2.1).symm (j, side)
  exact ⟨(congrArg (fun z : Fin (socketDir).groups × Fin (WideMemory.H x.h v.W k v.wideJobs) =>
      z.1.val) atSocket).trans (actual.owner x.formats.2.1 j side),
    (congrArg Prod.snd atSocket).trans
      (FundedCutRows.port_read v x tapeSize π input unitCost raw geometry actual j side)⟩

end SelectedShelfSockets
open Lean Meta Elab Term in
/-- Specialize the paid view using the checkout already embedded in the transported report. -/
local elab "fundedWidthForReport " reportId:ident tariffId:ident : term => do
  let reportLocal ← getLocalDeclFromUserName reportId.getId
  let some transported := reportLocal.value? | throwError "expected the retained output report"
  unless transported.isAppOf ``FixedProtocolFormat.Report.transportLedger do throwError "expected the report ledger transport"
  let selected := transported.getAppArgs[transported.getAppNumArgs-2]!
  let args := selected.getAppArgs
  let n := args.size
  unless n ≥ 11 do throwError "expected the signed report's checkout operands"
  let admittedPaid := args[n-6]!
  let mut receipt := admittedPaid.getAppArgs.back!
  unless receipt.isAppOf ``wide_reported_path_native do throwError "expected the original selected reported-path witness, got {receipt.getAppFn}"
  let mut receiptTy ← inferType receipt
  for _ in [:3] do
    let some ex ← whnfUntil receiptTy ``Exists | throwError "expected a funded checkout witness"
    let operands := ex.getAppArgs.push receipt
    let value := mkAppN (mkConst ``Classical.choose ex.getAppFn.constLevels!) operands
    receipt := mkAppN (mkConst ``Classical.choose_spec ex.getAppFn.constLevels!) operands
    receiptTy := ex.getAppArgs[1]!.beta #[value]
  let valid := Lean.Expr.proj ``And 0 receipt
  let budget := Lean.Expr.proj ``CalendarTerminalRoom 3 (← getFVarFromUserName tariffId.getId)
  return mkAppN budget #[args[n-11]!,args[n-7]!,args[n-10]!,args[n-9]!,admittedPaid,
    args[n-5]!,args[n-4]!,args[n-3]!,args[n-2]!,args[n-1]!,valid]


open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16384
set_option maxHeartbeats 9000000
set_option cleanup.letToHave false
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.BranchRoles Tagged.WideCalendarSites
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged.WideStack.Leaf ProtocolRAMReportedPorts
open Lean Meta in
private def selectedShelfSocketArguments (head : Lean.Expr) (precedingArgs : Array Lean.Expr)
    (chosen word site issuer socketPort socketRead roleFit widthPositive
      inject samePort laneBound privateBounds : Lean.Expr) : MetaM (Array Lean.Expr) := do
  unless precedingArgs.size == 39 do throwError "expected the funded shelf spine through capacity"
  let declType ← inferType head
  let nextDomain (xs : Array Lean.Expr) : MetaM Lean.Expr := do
    let mut t := declType
    for _ in [:xs.size] do
      unless t.isForall do throwError "short funded shelf spine"
      t := t.bindingBody!
    unless t.isForall do throwError "missing funded shelf operand"
    return t.bindingDomain!.instantiateRev xs
  let mut xs := precedingArgs ++ #[Lean.Expr.proj ``CalendarTerms.RankedRows 2 chosen, word, site]
  let fits ← forallBoundedTelescope (← nextDomain xs) (some 2) fun vs _ => do
    unless vs.size == 2 do throwError "expected fiber and side for the shelf role"
    mkLambdaFVars vs (mkApp2 roleFit (Lean.Expr.proj ``Subtype 0 vs[0]!) vs[1]!)
  let it := (← inferType issuer).consumeMData
  unless it.isAppOf ``CatalogueRows.Alignment do throwError "expected the selected issuer alignment"
  let original := it.getAppArgs.back!
  unless original.isAppOf ``CatalogueRows.Board.original do throwError "missing the original ordinal map"
  xs := xs ++ #[fits, original.getAppArgs.back!, issuer]
  let origType := (← nextDomain xs).consumeMData
  unless origType.isAppOfArity ``Equiv 2 do throwError "expected the original row equivalence"
  let row := origType.getAppArgs[1]!
  let orig := mkApp (mkConst ``Equiv.refl [← getLevel row]) row
  xs := xs.push orig
  let widths ← forallBoundedTelescope (← nextDomain xs) (some 1) fun vs equality => do
    let equality := equality.consumeMData
    unless vs.size == 1 && equality.isAppOfArity ``Eq 3 do throwError "expected the original-row width equality"
    let args := equality.getAppArgs
    let refl := mkApp2 (mkConst ``Eq.refl equality.getAppFn.constLevels!) args[0]! args[2]!
    mkLambdaFVars vs refl
  xs := xs ++ #[widths, widthPositive, inject, socketPort, samePort]
  for component in [0,1] do
    let projected ← forallBoundedTelescope (← nextDomain xs) (some 2) fun vs _ => do
      unless vs.size == 2 do throwError "expected one purchased row and its side"
      mkLambdaFVars vs (Lean.Expr.proj ``And component (mkAppN socketRead vs))
    xs := xs.push projected
  xs := xs.push laneBound
  let bounded ← forallBoundedTelescope (← nextDomain xs) (some 1) fun vs _ => do
    unless vs.size == 1 do throwError "expected a private row"
    let ord := Lean.Expr.proj ``Subtype 0 vs[0]!
    mkLambdaFVars vs (mkApp (Lean.Expr.proj ``And 0 privateBounds) ord)
  return xs.push bounded


open Lean Meta in
private def endpointShelfSuffix (target paidShelf signs roleFit oldWidths newWidths outputView rolesRoom digitRoom dense : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let eqn := target.consumeMData.headBeta
  unless eqn.isAppOfArity ``Eq 3 do throwError "expected the terminal equality"
  let value := eqn.getAppArgs[1]!.consumeMData
  unless value.isAppOfArity ``ThreeFlat.Routing.TypedWiring.value 6 do throwError "expected the terminal circuit evaluation"
  let net := value.getAppArgs[4]!.consumeMData
  unless net.isAppOfArity ``Tagged.WideControlJoin.Gate.shelfNet 16 do throwError "expected the exposed terminal shelf circuit"
  let gateArgs := net.getAppArgs
  let assignment := value.getAppArgs[5]!.consumeMData.headBeta
  let (externalPins, selectedPins) ← if assignment.isAppOfArity ``Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms.readPins 10 then
      pure (assignment.getAppArgs[6]!, assignment.getAppArgs[7]!)
    else do
      let some outer ← whnfUntil assignment ``Sum.elim | throwError "expected physical input pins"
      let some paidInnerInputs ← whnfUntil outer.appArg! ``Sum.elim | throwError "expected the selected date pins"
      pure (outer.appFn!.appArg!, paidInnerInputs.appFn!.appArg!)
  let fields := Lean.Expr.proj ``And 0 paidShelf
  let shelfRoom := Lean.Expr.proj ``And 1 paidShelf
  let some receipt ← whnfUntil (← inferType fields) ``Hierarchy.ProbeStage.CoreBoard.Report.ShelfContents
    | throwError "expected the paid shelf contents"
  let shelf := receipt.getAppArgs
  unless shelf.size == 17 do throwError "unexpected physical shelf shape"
  return #[gateArgs[2]!, gateArgs[3]!, gateArgs[5]!, gateArgs[6]!, gateArgs[8]!,
    shelf[11]!, shelf[12]!, shelf[13]!, shelf[14]!, externalPins, selectedPins,
    fields, Lean.Expr.proj ``And 0 signs, Lean.Expr.proj ``And 1 signs, roleFit, oldWidths,
    newWidths, outputView, rolesRoom, digitRoom, dense, shelfRoom]

open Lean Meta in
private def endpointFinalShelfOperands (target paidShelf signs roleFit oldWidths outputView tariff : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let capacity := Lean.Expr.proj ``CalendarTerminalRoom 2 tariff
  let outputTy ← whnf (← inferType outputView)
  unless outputTy.isForall do throwError "expected a width proof for every output row"
  let capTy := (← inferType capacity).consumeMData.headBeta
  let newWidths ← withLocalDeclD `row outputTy.bindingDomain! fun row => do
    let bounded := mkApp outputView row
    let boundTy := (← inferType bounded).consumeMData.headBeta
    let trans := mkAppN (mkConst ``Nat.le_trans) #[boundTy.appFn!.appArg!, boundTy.appArg!, capTy.appArg!, bounded, capacity]
    mkLambdaFVars #[row] trans
  let bound := Lean.Expr.proj ``And 1 paidShelf
  let limit := (← inferType bound).consumeMData.headBeta.appArg!
  let dense ← withLocalDeclD `address (mkApp (mkConst ``Fin) limit) fun address => do
    mkLambdaFVars #[address] (← mkEqRefl (mkApp2 (mkConst ``Fin.val) limit address))
  endpointShelfSuffix target paidShelf signs roleFit oldWidths newWidths outputView
    (Lean.Expr.proj ``CalendarTerminalRoom 0 tariff) (Lean.Expr.proj ``CalendarTerminalRoom 1 tariff) dense



open Lean Meta in
private def endpointShelfFirstOperands (target selectedAllocation reportValue aligned purchasedFits packed selectedStates offeredDir : Lean.Expr) :
    MetaM (Array Lean.Expr) := do
  let valueTerm := target.consumeMData.headBeta.getAppArgs[1]!.consumeMData
  let shelfNetExpr := valueTerm.getAppArgs[4]!.consumeMData
  let rankedTy ← whnf (← inferType selectedAllocation)
  let reportTy ← whnf (← inferType reportValue)
  let issuerTy ← inferType aligned
  unless rankedTy.isAppOfArity ``CalendarTerms.RankedRows 13 && reportTy.isAppOfArity ``CoreBoard.Report 9 &&
      issuerTy.isAppOfArity ``CatalogueRows.Alignment 13 && shelfNetExpr.getAppNumArgs == 16 do
    throwError "expected a funded allocation, report, issuer alignment and terminal shelf"
  let kA := rankedTy.getAppArgs
  let rA := reportTy.getAppArgs
  let aA := issuerTy.getAppArgs
  let gA := shelfNetExpr.getAppArgs
  let choices ← inferType selectedStates
  let some choicesTy ← whnfUntil choices ``SiteChoices | throwError "expected the selected site histories"
  let hist := choicesTy.getAppArgs
  let t := hist.size
  let cursorTy ← inferType hist[t-2]!
  let header : Array Lean.Expr := #[kA[0]!,kA[1]!,aA[1]!,cursorTy,rA[0]!,aA[1]!,rA[3]!,rA[4]!,rA[5]!,
    aA[3]!,rA[6]!,rA[7]!,kA[6]!,kA[7]!,kA[9]!,kA[11]!,gA[gA.size-5]!,gA[gA.size-4]!]
  let priceTy ← whnf (← inferType purchasedFits)
  unless priceTy.isForall do throwError "expected a purchase at every live end"
  let lastPoint := priceTy.bindingBody!.getAppArgs.back!
  let chargedRole := lastPoint.appArg!
  let some selectedPorts := chargedRole.find? (fun node => node.isApp && node.isAppOf ``Terminal.ports)
    | throwError "expected the charged physical end"
  let ends := selectedPorts.getAppArgs.push chargedRole.appArg!
  let pCount := ends.size
  let packedTy ← inferType packed
  let some placement ← whnfUntil packedTy ``Eq | throwError "expected the packed terminal equation"
  let leftSide := placement.getAppArgs[1]!
  unless leftSide.isApp && leftSide.getAppFn.isConstOf ``widePathCells do throwError "expected the selected path cells"
  let oldOrd := aA.back!
  unless oldOrd.isAppOf ``CatalogueRows.Board.original do throwError "expected the issued original selector"
  return header ++ #[rA[1]!,ends[pCount-9]!,aA[8]!,ends[pCount-7]!,
    hist[t-5]!,hist[t-4]!,hist[t-3]!,hist[t-2]!,hist.back!,
    reportValue,ends[pCount-2]!,lastPoint.appFn!,purchasedFits,leftSide.appFn!,packed,selectedStates,
    offeredDir,aA[4]!,oldOrd.getAppArgs[oldOrd.getAppNumArgs-2]!,aA[10]!,Lean.Expr.proj ``CalendarTerms.RankedRows 3 selectedAllocation]

open Lean Meta Elab Tactic in
local elab "applyFundedEndpointShelf" " with " picked:ident reportArg:ident alignmentArg:ident
    fitsArg:ident packingArg:ident wordArg:ident historyArg:ident siteArg:ident portArg:ident
    socketsArg:ident signsArg:ident tariffArg:ident paidShelfArg:ident oldWidthArg:ident outputViewArg:ident
    " via " "[" dirArg:term "," labelledArg:term "," widthArg:term "," injectArg:term ","
    portEqArg:term "," laneArg:term "," boundsArg:term "]" : tactic => withMainContext do
  let goal ← getMainGoal
  let targetTy ← goal.getType
  let [chosen, reportValue, issuer, fit, packing, word, histories, physicalSiteExpr, port, sockets, signs, tariff, paidShelf, oldWidths, outputView] ←
    [picked,reportArg,alignmentArg,fitsArg,packingArg,wordArg,historyArg,siteArg,portArg,socketsArg,signsArg,tariffArg,paidShelfArg,oldWidthArg,outputViewArg].mapM
      (fun id => getFVarFromUserName id.getId) | throwError "expected the funded shelf locals"
  let [offeredDir, labelBound, positiveWidth, inject, samePort, lanes, privateBudget] ←
    [dirArg,labelledArg,widthArg,injectArg,portEqArg,laneArg,boundsArg].mapM
      (fun operand => do instantiateMVars (← Lean.Elab.Term.elabTerm operand none)) | throwError "expected the paid register bounds"
  let proc := mkConst ``CoreBoard.Report.funded_shelf_finish [.zero]
  let first ← endpointShelfFirstOperands targetTy chosen reportValue issuer fit packing histories offeredDir
  let middle ← selectedShelfSocketArguments proc first chosen word physicalSiteExpr issuer port sockets labelBound positiveWidth inject samePort lanes privateBudget
  let endArgs ← endpointFinalShelfOperands targetTy paidShelf signs labelBound oldWidths outputView tariff
  let allArgs := middle ++ endArgs
  unless allArgs.size == 77 do throwError "expected 77 actual shelf operands, got {allArgs.size}"
  let application ← instantiateMVars (mkAppN proc allArgs)
  if application.hasMVar then throwError "the original funded shelf application has unresolved operands"
  goal.assign application
  replaceMainGoal []

/-- Reconcile two presentations of a receipt test while the allocation is a variable. -/
private theorem endpointThroughRows {RowType : Type} (P Q : RowType → Prop)
    (fromRow toRow : RowType) (same : fromRow = toRow)
    (adapt : ∀ r, P r → Q r) (valid : P fromRow) : Q toRow :=
  same ▸ adapt fromRow valid

open Lean Meta Elab Term in
/-- The telescope of `onBranch`, extended with another proof of its row-board equality.
Its conclusion equates the resulting move to the original selected-branch application. -/
local elab "endpointBranchSpellingType" : term => do
  let decl ← getConstInfo ``CalendarTerms.RankedRows.onBranch
  let branchFn := Lean.mkConst decl.name (decl.levelParams.map Level.param)
  forallTelescope decl.type fun xs _ => do
    let branchTerm := mkAppN branchFn xs
    let moved := (decl.value!.beta xs).consumeMData
    unless moved.isAppOf ``CalendarTerms.RankedRows.move do
      throwError "expected onBranch to be one ranked-row move"
    let sameType ← inferType moved.appFn!.appArg!
    withLocalDeclD `rowProof sameType fun rowProof => do
      let alternate := mkApp2 moved.appFn!.appFn! rowProof moved.appArg!
      mkForallFVars (xs.push rowProof) (← mkEq alternate branchTerm)

private theorem endpointMoveEqualsBranch : endpointBranchSpellingType := by
  intros
  rfl

open Lean Meta Elab Tactic in
/-- Transport the downstream check along the equality of the selected reports. -/
local elab "moveExactEndpointReport " sameId:ident rowsId:ident allocationId:ident testId:ident : tactic =>
    withMainContext do
  let sameProof ← getFVarFromUserName sameId.getId
  let rowsProof ← getFVarFromUserName rowsId.getId
  let allocator ← getFVarFromUserName allocationId.getId
  let testExpr ← getFVarFromUserName testId.getId
  let eqType := (← inferType sameProof).consumeMData
  unless eqType.isAppOfArity ``Eq 3 do throwError "expected equality of reports"
  let eqArgs := eqType.getAppArgs
  let reportTy ← whnf eqArgs[0]!
  unless reportTy.isAppOfArity ``CoreBoard.Report 9 do throwError "expected the paid report family"
  let rankTy ← whnf (← inferType allocator)
  unless rankTy.isAppOfArity ``CalendarTerms.RankedRows 13 do throwError "expected the selected row allocation"
  let rArgs := reportTy.getAppArgs
  let sArgs := rankTy.getAppArgs
  let goal ← getMainGoal
  let reached ← mkFreshExprSyntheticOpaqueMVar (mkApp2 testExpr eqArgs[2]! allocator) (← goal.getTag)
  let step := mkAppN (mkConst ``CalendarTerms.RankedRows.move_report) #[
    rArgs[0]!, rArgs[2]!, rArgs[3]!, rArgs[4]!, rArgs[5]!, rArgs[6]!, rArgs[7]!, rArgs[1]!,
    sArgs[0]!, sArgs[1]!, sArgs[2]!, sArgs[5]!, sArgs[6]!, sArgs[7]!, sArgs[9]!, sArgs[10]!,
    sArgs[11]!, sArgs[3]!, sArgs[4]!, rArgs[8]!, eqArgs[1]!, eqArgs[2]!, sameProof, rowsProof,
    allocator, testExpr, reached]

  let some checked ← withTransparency .all <| whnfUntil (← goal.getType) ``CalendarTerms.RankedRows.Check
    | throwError "expected the original calendar endpoint check"
  let operands := checked.getAppArgs
  let rowIndex := operands.size - 3
  let destination := operands[rowIndex]!
  unless destination.isAppOf ``CalendarTerms.RankedRows.onBranch do
    throwError "expected the selected rank's original onBranch allocation"
  let domain ← inferType destination
  let destinationTest := mkLambda `allocation .default domain
    (mkAppN checked.getAppFn (operands.set! rowIndex (.bvar 0)))
  let sourceTest := mkApp testExpr eqArgs[1]!
  let resultType := (← inferType step).consumeMData
  unless resultType.isApp && resultType.appFn! == sourceTest do
    throwError "unexpected report transport conclusion"
  let transported := resultType.appArg!
  let rowEquality := mkAppN (mkConst ``endpointMoveEqualsBranch)
    (destination.getAppArgs.push rowsProof)
  let adapt := mkLambda `allocation .default domain
    (mkLambda `valid .default (mkApp sourceTest (.bvar 0)) (.bvar 0))
  let finalProof := mkAppN (mkConst ``endpointThroughRows)
    #[domain, sourceTest, destinationTest, transported, destination, rowEquality, adapt, step]
  goal.assign finalProof
  replaceMainGoal [reached.mvarId!]

attribute [local irreducible] Nat.pow
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
variable (height : v.BranchRoleHeight h width) (tariff : v.CalendarTerminalRoom x)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unit cpu.room).2
local notation "W" => Native.wordBits h d Native.copies
local notation "root" => (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix sl es (base perm) es (base perm))
local notation "tree" => Prefix.cursorSlot (slot:=sl) (events:=es) (x₀:=base perm)
local notation "ws" => Prefix.atWidth ((Z).width perm)
local notation "top" => Prefix.atCursor root
local notation "branch" => Prefix.histories root path
local notation "stop" => WireTelescope.CalendarTape.terminal tree es top branch
local notation "input" => (reader).format.windows.header es record seed
local notation "bill" => v.wide_reported_path_native h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words path
local notation "admitted" => (bill).choose
local notation "cost" => (bill).choose_spec.choose
local notation "names" => fun {entries : ℕ} (owners : Fin entries → Fin (Fintype.card (Columns h (2^v.W)) * k))
  (fees : Fin entries → ℕ) => (bill).choose_spec.choose_spec.choose owners fees
local notation "native" => v.signedPathNativeReport h width S perm.symm input v.maxBits Sfit admitted
  cpu.ready.credit cpu.ready.size_le cost (0:Word W) names
local notation "runAt" => v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "out" => (runAt).2.2.2.choose
local notation "actual" => endpointPaidFunding
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
local notation "replayed" => cursorReport perm ((Z).width perm) ((Z).reported perm) branch
local notation "Rpt" => CoreBoard.Report perm d k width (fuel v.mesh*width) v.radius 1 (ws stop)
local notation "table" r:arg => (⟨(r).edges,(r).rows⟩ : CalendarTerms.RowBoard)
local notation "plan" r:arg => CalendarTerms.RankedRows (F:=F) (geom).index D (dir).groups ports (2^ell) width m times view (table r)

attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit

open Lean Elab Term in
/-- Read the arguments of the reconciliation selected by the native run. -/
private def nativeReceiptArg (name : Name) (idx : Nat) : TermElabM Lean.Expr := do
  let receipt ← Meta.getFVarFromUserName name
  let rt ← Meta.whnf (← Meta.inferType receipt)
  unless rt.getAppFn.isConstOf ``Whole.Reconciliation do throwError "expected settlement reconciliation"
  return rt.getAppArgs[rt.getAppNumArgs-idx]!
open Lean Elab Term in
local elab "shelfIssues " cert:ident : term => do
  let recordCount ← nativeReceiptArg cert.getId 11
  let counted ← Meta.whnf recordCount
  unless counted.getAppFn.isConstOf ``CatalystArchive.recordCount do throwError "expected record count"
  return counted.getAppArgs.back!
open Lean Elab Term in
local elab "shelfSite " cert:ident : term => nativeReceiptArg cert.getId 6
open Lean Elab Term in
local elab "shelfDebit " cert:ident : term => nativeReceiptArg cert.getId 5

open Lean Meta Elab Tactic in
/-- Read the allocation and its funding from the selected endpoint. -/
local elab "retainEndpointRows " chosenId:ident " with " fundedId:ident : tactic => withMainContext do
  let endpointGoalExpr ← getMainTarget
  let checked ← if endpointGoalExpr.isAppOf ``CalendarTerms.RankedRows.Check then pure endpointGoalExpr
    else withTransparency .reducible <| whnf endpointGoalExpr
  let found := do
    _root_.guard (checked.isAppOf ``CalendarTerms.RankedRows.Check)
    let branchRankExpr ← checked.getAppArgs[checked.getAppNumArgs-3]?
    _root_.guard (branchRankExpr.isAppOf ``CalendarTerms.RankedRows.onBranch)
    let rowAllocationExpr ← branchRankExpr.getAppArgs.back?
    _root_.guard (rowAllocationExpr.isAppOf ``FundedCutRows.rowData)
    return rowAllocationExpr
  let found := found <|> checked.find? fun e => e.isAppOf ``FundedCutRows.rowData
  let some allocation := found | throwError "expected the selected endpoint row allocation"
  let rec getOperand (ty : Lean.Expr) (xs : List Lean.Expr) : TacticM Lean.Expr := do
    match ty, xs with
    | .forallE nm _ body _, operand :: rest =>
      if nm == `actual then return operand
      getOperand body rest
    | _, _ => throwError "expected the paid cutrows operand in the selected allocation"
  let allocationDecl ← getConstInfo ``FundedCutRows.rowData
  let funding ← getOperand allocationDecl.type allocation.getAppArgs.toList
  let goal ← getMainGoal
  let (_, nextGoal) ← (← goal.define chosenId.getId (← inferType allocation) allocation).intro1P
  let result ← nextGoal.withContext do
    (← nextGoal.define fundedId.getId (← inferType funding) funding).intro1P
  let retainedPlace := checked.getAppArgs[checked.getAppNumArgs-2]!
  let placed ← result.2.withContext do
    (← result.2.define `endpointOriginalPlace (← inferType retainedPlace) retainedPlace).intro1P
  replaceMainGoal [placed.2]

open Lean Meta Elab Tactic in
/-- Obtain equality of the purchased and issuer alignments at their exact retained indices. -/
local elab "retainEndpointAlignment " sameId:ident fmt:ident ht:term:arg span:term:arg lhs:ident rhs:ident : tactic =>
    withMainContext do
  let family ← getFVarFromUserName fmt.getId
  let heightVal ← elabTerm ht none
  let widthVal ← elabTerm span none
  let purchasedVal ← getFVarFromUserName lhs.getId
  let issuerVal ← getFVarFromUserName rhs.getId
  let issuerType := (← inferType issuerVal).consumeMData
  let formatType := (← inferType family).consumeMData
  unless issuerType.getAppFn.isConstOf ``CatalogueRows.Alignment do
    throwError "expected the issuer catalogue alignment"
  unless formatType.getAppFn.isConstOf ``FixedProtocolFormat do
    throwError "expected the fixed protocol format"
  let components := issuerType.getAppArgs
  let n := components.size
  let proof := mkAppN (mkConst ``wide_sourceAlignment_unique) (formatType.getAppArgs ++
    #[family, heightVal, widthVal, components[n-7]!, components[n-5]!, components[n-3]!,
      components[n-4]!, components[n-2]!, purchasedVal, issuerVal])
  let equality := mkApp3 (mkConst ``Eq [.succ .zero]) issuerType purchasedVal issuerVal
  let goal ← getMainGoal
  let (_, nextGoal) ← (← goal.assert sameId.getId equality proof).intro1P
  replaceMainGoal [nextGoal]

open Lean Meta Elab Term in
/-- Reuse the role construction whose marks index the issuer's alignment. -/
local elab "endpointPacking " issuer:ident : term => do
  let aligned ← getFVarFromUserName issuer.getId
  let alignmentTy ← inferType aligned
  unless alignmentTy.getAppFn.isConstOf ``CatalogueRows.Alignment do
    throwError "expected the issuer catalogue alignment"
  let args := alignmentTy.getAppArgs
  let marks := args[args.size-5]!
  let some pathRoleExpr := marks.find? (fun e => e.isAppOfArity ``widePathRoles 25)
    | throwError "expected the signed path role construction"
  let packing ← mkConstWithFreshMVarLevels ``wide_path_terminal_packing
  return mkAppN packing (pathRoleExpr.getAppArgs.push aligned)


private theorem endpointSitesOfEquiv {SourceSite NumberedSite : Type} (number : SourceSite ≃ NumberedSite)
    (condition : NumberedSite → Prop) (each : ∀ x, condition (number x)) : ∀ y, condition y :=
  number.surjective.forall.mpr each

open Lean Meta Elab Tactic in
/-- Introduce a physical site by traversing the actual catalogue site's enumeration. -/
local elab "indexEndpointSites " numbering:term:arg : tactic => withMainContext do
  let enumeration ← elabTerm numbering none
  let enumerationType ← whnf (← inferType enumeration)
  unless enumerationType.isAppOfArity ``Equiv 2 do throwError "expected the physical site enumeration"
  let srcType := enumerationType.getAppArgs[0]!
  let dstType := enumerationType.getAppArgs[1]!
  let goal ← getMainGoal
  let .forallE name ty predicate info ← whnf (← goal.getType) | throwError "expected the numbered site quantifier"
  let condition := Lean.Expr.lam name ty predicate info
  let readSite := mkApp3 (mkConst ``Equiv.toFun enumerationType.getAppFn.constLevels!) srcType dstType enumeration
  let eachType ← withLocalDeclD `physicalSite srcType fun x => mkForallFVars #[x] (mkApp condition (mkApp readSite x))
  let each ← mkFreshExprSyntheticOpaqueMVar eachType (← goal.getTag)
  goal.assign (mkAppN (mkConst ``endpointSitesOfEquiv) #[srcType,dstType,enumeration,condition,each])
  replaceMainGoal [each.mvarId!]

open Lean Meta Elab Term in
/-- Specialize a funded row projection at the actual parameters of the retained allocation. -/
local elab "retainedFunding " allocationId:ident field:term:arg : term => do
  let localAllocation ← getLocalDeclFromUserName allocationId.getId
  let some selectedRows := localAllocation.value? | throwError "expected the retained row allocation"
  unless selectedRows.isAppOf ``FundedCutRows.rowData do throwError "expected funded cut rows"
  let fieldExpr ← elabTerm field none
  let mut sourceTy := (← getConstInfo ``FundedCutRows.rowData).type
  let mut parameters : Std.HashMap Lean.Name Lean.Expr := {}
  let mut fieldInstance : Option Lean.Expr := none
  for operand in selectedRows.getAppArgs do
    let .forallE nm _ body binder := sourceTy | throwError "expected a funded row parameter"
    parameters := parameters.insert nm.eraseMacroScopes operand
    if binder.isInstImplicit then fieldInstance := some operand
    sourceTy := body
  let mut fieldTy ← inferType fieldExpr
  let mut resultExpr := fieldExpr
  while fieldTy.isForall do
    let replacement := if fieldTy.binderInfo.isInstImplicit then fieldInstance
      else parameters[fieldTy.bindingName!.eraseMacroScopes]?
    let some param := replacement | return resultExpr
    resultExpr := mkApp resultExpr param
    fieldTy := fieldTy.bindingBody!
  return resultExpr

open Lean Elab Term in
/-- Apply the funded shelf statement to the issued alignment and its exclusivity proof. -/
local elab "endpointFundedSockets " fn:term:arg " [" issuerId:ident "," sameId:ident "," exProof:term "]" : term => do
  let partialField ← elabTerm fn none
  let issuedAlignment ← Lean.Meta.getFVarFromUserName issuerId.getId
  let equalityProof ← Lean.Meta.getFVarFromUserName sameId.getId
  let exclusiveArg ← elabTerm exProof none
  return mkAppN partialField #[issuedAlignment, equalityProof, exclusiveArg]

open Lean Elab Term Meta in
local elab "selectFinalShelfColumns " obtained:term "," sitesTerm:term "," paidLimit:term : term => do
  let purchased := (← instantiateMVars (← elabTerm obtained none)).consumeMData
  unless purchased.isAppOf ``wide_selected_local_return do throwError "expected the selected local return"
  let receipt := mkAppN (← mkConstWithFreshMVarLevels ``wide_selected_shelf_contents) purchased.getAppArgs
  let columns := Lean.Expr.proj ``And 0 receipt
  let gateBound := Lean.Expr.proj ``And 1 (Lean.Expr.proj ``And 1 receipt)
  let some columnType ← whnfUntil (← inferType columns) ``CoreBoard.Report.ShelfContents
    | throwError "expected the original five shelf columns"
  let args := columnType.getAppArgs
  let outPos := args.size - 3
  let storedHeap := args[outPos]!
  let store := Lean.Expr.proj ``And 1 (Lean.Expr.proj ``And 1 (Lean.Expr.proj ``And 1 purchased))
  let some storeType ← whnfUntil (← inferType store) ``Exists | throwError "expected an issued output heap"
  let physicalHeap := mkAppN (mkConst ``Exists.choose storeType.getAppFn.constLevels!) (storeType.getAppArgs.push store)
  unless ← isDefEq storedHeap physicalHeap do throwError "shelf and returned memory differ"
  let routedType := mkAppN columnType.getAppFn (args.set! outPos physicalHeap)
  let siteCount ← elabTerm sitesTerm none
  let limit ← elabTerm paidLimit none
  let cells := mkApp2 (mkConst ``Nat.mul) siteCount args[outPos-3]!
  let shelfEnd := mkApp2 (mkConst ``Nat.add) args[outPos-1]! (mkApp2 (mkConst ``Nat.mul) (mkNatLit 5) cells)
  let expectedBound := mkApp2 (mkConst ``Nat.le) shelfEnd limit
  unless ← isDefEq expectedBound (← inferType gateBound) do throwError "unexpected paid shelf interval"
  return mkApp4 (mkConst ``And.intro) routedType expectedBound columns gateBound


open Lean Meta Elab Tactic in
/-- Expose the terminal shelf circuit at the selected site of the original calendar. -/
local elab "unfoldEndpointFinish" : tactic => withMainContext do
  let goal ← getMainGoal
  let initial := (← goal.getType).consumeMData.headBeta
  let eqTerm ← if initial.isAppOfArity ``Eq 3 then pure initial
    else withTransparency .reducible <| whnf initial
  unless eqTerm.isAppOfArity ``Eq 3 do throwError "expected the terminal equality"
  let valueTerm := eqTerm.appFn!.appArg!.consumeMData
  unless valueTerm.isAppOf ``TypedWiring.value do throwError "expected the terminal gate evaluation"
  let gateTerm := valueTerm.appFn!.appArg!.consumeMData
  unless gateTerm.isApp do throwError "expected a finish circuit applied to a site"
  let finishFn := gateTerm.appFn!.consumeMData
  let siteIndex := gateTerm.appArg!
  let sitesTerm ← match finishFn with
    | .proj structName 2 receiver =>
      unless structName == ``SignedSites do throwError "expected the SignedSites finish projection"
      pure receiver
    | other =>
      unless other.isAppOf ``SignedSites.finish do throwError "expected SignedSites.finish"
      pure other.appArg!
  let some recordTerm ← delta? sitesTerm.consumeMData (· == ``SignedSites.ofCalendar)
    | throwError "expected the owned calendar gate family"
  let recordTerm := recordTerm.consumeMData
  unless recordTerm.isAppOf ``SignedSites.mk do throwError "expected the signed calendar constructor"
  let some finishTerm ← projectCore? recordTerm 2
    | throwError "missing the finish field of the signed calendar"
  let shelfTerm := (finishTerm.consumeMData.beta #[siteIndex]).consumeMData
  unless shelfTerm.isAppOf ``Tagged.WideControlJoin.Gate.shelfNet do
    throwError "expected the terminal shelf network"
  let valueNew := mkApp2 valueTerm.appFn!.appFn! shelfTerm valueTerm.appArg!
  let eqNew := mkApp2 eqTerm.appFn!.appFn! valueNew eqTerm.appArg!
  let nextGoal ← goal.replaceTargetDefEq eqNew
  replaceMainGoal [nextGoal]

private theorem endpointShelfInputTransport {LensT OrderT ValueT : Type}
    (readShelfAt : LensT → OrderT → ValueT) {lensBefore lensAfter : LensT}
    {ordBefore ordAfter : OrderT} {wantedValue : ValueT}
    (lensEq : lensBefore = lensAfter) (ordEq : ordBefore = ordAfter)
    (remaining : readShelfAt lensAfter ordAfter = wantedValue) :
    readShelfAt lensBefore ordBefore = wantedValue :=
  (congrArg (fun x => readShelfAt x ordBefore) lensEq).trans
    ((congrArg (readShelfAt lensAfter) ordEq).trans remaining)

open Lean Meta Elab Tactic in
/-- Substitute the aperture and numbering at their two terminal shelf operands. -/
local elab "alignEndpointShelf " siteId:ident numberingId:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let currentEq := (← goal.getType).consumeMData.headBeta
  unless currentEq.isAppOfArity ``Eq 3 do throwError "expected the exposed terminal equality"
  let eqArgs := currentEq.getAppArgs
  let gateValue := eqArgs[1]!.consumeMData
  unless gateValue.isAppOf ``TypedWiring.value do throwError "expected the shelf evaluation"
  let network := gateValue.appFn!.appArg!.consumeMData
  unless network.isAppOf ``Tagged.WideControlJoin.Gate.shelfNet do throwError "expected the terminal shelf network"
  let pinRead := gateValue.appArg!.consumeMData
  unless pinRead.isAppOfArity ``CalendarTerms.readPins 10 do throwError "expected the terminal readPins operands"
  let sourceLens := network.appArg!.consumeMData.headBeta
  unless sourceLens.isAppOf ``calendarTerminalPins do throwError "expected the actual calendar aperture"
  let locatedSite ← getFVarFromUserName siteId.getId
  let lensProof := mkApp (mkAppN (mkConst ``calendar_terminal_pins) sourceLens.appFn!.getAppArgs) locatedSite
  let numberingProof ← getFVarFromUserName numberingId.getId
  let lensProofTy := (← inferType lensProof).consumeMData
  let numberingProofTy := (← inferType numberingProof).consumeMData
  unless lensProofTy.isAppOfArity ``Eq 3 && numberingProofTy.isAppOfArity ``Eq 3 do
    throwError "expected aperture and numbering equalities"
  let lensSides := lensProofTy.getAppArgs
  let ordSides := numberingProofTy.getAppArgs
  let pinArgs := pinRead.getAppArgs
  let assemble (l o : Lean.Expr) : Lean.Expr :=
    mkApp2 gateValue.appFn!.appFn! (mkApp network.appFn! l)
      (mkAppN pinRead.getAppFn (pinArgs.set! 5 o))
  let reading := mkLambda `shelfAperture .default lensSides[0]!
    (mkLambda `shelfOrder .default ordSides[0]! (assemble (.bvar 1) (.bvar 0)))
  let residual := mkApp2 currentEq.appFn!.appFn! (assemble lensSides[2]! ordSides[2]!) eqArgs[2]!
  let remaining ← mkFreshExprSyntheticOpaqueMVar residual (← goal.getTag)
  let transport := mkAppN (mkConst ``endpointShelfInputTransport)
    #[lensSides[0]!,ordSides[0]!,eqArgs[0]!,reading,sourceLens,lensSides[2]!,
      pinArgs[5]!,ordSides[2]!,eqArgs[2]!,lensProof,numberingProof,remaining]
  goal.assign transport
  replaceMainGoal [remaining.mvarId!]


/-- On a surviving original checkout the five literal terminal columns select
the real input and output digits of the reported matrix at every site. -/
theorem calendar_endpoint_finish {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
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
    (height : v.BranchRoleHeight h width) (tariff : v.CalendarTerminalRoom x) :
    v.wideCalendarEndpointField (C:=C) m ell short u δ ξ x cpu room control support
      Z (fun _ _=>rfl) prices pricePos groupsFit metadata lanesFit buy e perm i tag height
      (fun _=>rfl) .finish := by
  intro kept
  retainEndpointRows chosen with endpointPaidFunding
  let purchased := (actual).sourceAlignment
  let baseline := (Classical.choose_spec (v.wide_funded_run_at h width v.radius perm.symm input v.maxBits S Sfit
    admitted cpu.ready.credit cpu.ready.size_le (0:Word W))).1
  let rowsAt := shelfIssues baseline
  let sourceAt := shelfSite baseline
  let debitAt := shelfDebit baseline
  let paidAlignment := names sourceAt debitAt
  let issuerAlignment : CatalogueRows.Alignment b v.sampler perm.symm v.depth (shape).mark v.radius (native).rows
    (fun edgeIndex=>((native).rows edgeIndex).width) ((b).original v.sampler perm.symm v.depth (shape).mark order
      (v.wideBoughtOrdinal h width perm.symm (shape).mark)) := paidAlignment.1.some
  retainEndpointAlignment sameNames v h width purchased issuerAlignment
  let packed := endpointPacking issuerAlignment
  let head := Classical.choose packed
  let fits := Classical.choose packed.choose_spec
  have packing := packed.choose_spec.choose_spec
  let finalReport : Rpt := FixedProtocolFormat.Report.transportLedger native head
  have complete : replayed=finalReport := report_eq_of_bundle perm
    ((cursor_report_bundle perm ((Z).width perm) ((Z).reported perm) path).trans (runAt).1) head
  let eqrows := congrArg (fun r:Rpt=>table r) complete
  let check := fun (r:Rpt) (allocation:plan r) => ∀(a : (j:Fin r.edges)→Fin (2^(r.rows j).width))
    (q : SiteChoices tree ws es top branch) s, TypedWiring.value ((sites).finish s)
      (CalendarTerms.readPins (B:=G) allocation.numbering e record ((G).terminal out)
        (nativePins («view»:=view) (geom).index r.rows allocation.positive allocation.stage allocation.installed
          allocation.cap a (placedBits tree ws es top branch endpointOriginalPlace q))) =
      r.finish s (WideCalendarSites.last tree ws s es top branch (q s).1 (q s).2) (r.ports a s)
  moveExactEndpointReport complete eqrows chosen check
  intro a q
  indexEndpointSites (CoreBoard.siteNumber h d k)
  intro loc
  let port := retainedFunding chosen (@FundedCutRows.port)
  have sockets := endpointFundedSockets (retainedFunding chosen (@FundedCutRows.selected_shelf_sockets)) [issuerAlignment, sameNames, (shape).exclusive]
  have signs := v.wide_funded_shelf_endpoints («h»:=h) («width»:=width) (size:=S) (M:=v.radius)
    (π:=perm.symm) (raw:=input) (bits:=v.maxBits) (horizon:=Sfit) (age:=admitted)
    (budget:=cpu.ready.credit) (small:=cpu.ready.size_le) (marks:=(shape).mark)
    (unique:=(shape).exclusive) (A₀:=issuerAlignment) (issues:=rowsAt) (who:=sourceAt)
    (baseline:=baseline) (read:=paidAlignment.2) («cost»:=cost)
  have numbered : chosen.numbering=Equiv.refl _ :=
    CalendarTerms.privateWorkspace_refl (geom).index (fun _ : (b).Private order => v.widePrivateUnit unit * width) roles (dir).groups ports (2^ell) ((es).length+1) view width
  unfoldEndpointFinish
  alignEndpointShelf loc numbered
  have tariffCeilings := HistoryRoles.ceiling_le («h»:=h) («W»:=v.W) (k:=k)
    (attempts:=v.wideJobs) v.sampler v.mesh unit v.keepLimit (fuel v.mesh) width
  let storedBits := SettledMatrix.Layout.bits finalReport.fixed finalReport.stock finalReport.reserved finalReport.used
  have storedWidths : ∀ j, storedBits j ≤ 2^TurnShelf.exponent (v.calendarTerminalWidth*width) := by
    intro j
    by_cases positive : 0 < storedBits j
    · let charged : NamedAperture.LiveEnd storedBits := ⟨(j,false),positive⟩
      exact (fits charged).trans ((tariffCeilings _).trans tariff.capacity)
    · exact (Nat.eq_zero_of_not_pos positive).le.trans (Nat.zero_le _)
  let paidShelf := selectFinalShelfColumns (runAt), (siteLast h d k + 1), ((G).u)
  let terminalView := fundedWidthForReport finalReport tariff
  applyFundedEndpointShelf with chosen finalReport issuerAlignment fits packing a q loc port sockets signs tariff paidShelf storedWidths terminalView via
    [dir, v.wide_shelf_role_fit h, x.formats.2.1,
      retainedFunding chosen (@FundedCutRows.shelf_injective), retainedFunding chosen (@FundedCutRows.shelf_port),
      retainedFunding chosen (@FundedCutRows.shelf_lanes),
      (v.wide_selected_private_bounds m ell short u δ ξ unit x cpu v.calendarUnit_rate support perm path)]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
