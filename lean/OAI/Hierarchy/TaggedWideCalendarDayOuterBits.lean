import OAI.Hierarchy.TaggedWidePathOuterBits
import OAI.Hierarchy.TaggedWideCalendarDayPins
import OAI.Hierarchy.TaggedWideCarriedCast
import OAI.Hierarchy.TaggedWirePacketNeighborMetadata

namespace OAI
/-! # Complete source and destination reads of the selected physical date -/

-- The full purchase telescope makes automatic premise indexing expensive for these reads.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "calendarDayPins_timed"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_calendar_day_outer_carried_bits"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_calendar_day_outer_rebased_bits"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_calendar_day_substep_carried_bits"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "calendar_day_spill_post_bits"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "calendar_feed_carried_bits"

noncomputable section
namespace Hierarchy.Tagged.WideCalendarSites
open ThreeFlat Routing
open ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts WideStack
open WideStack.Leaf
open scoped Classical

private theorem paidNativeHistoryDigit {F : Type*} [Field F] {T : Type} [Fintype T]
    {N groups ports lanes view w m n : ℕ} (key : T ↪ ℕ×ℕ)
    (raw : Fin N→ProtocolRAMEmit.Row) (positive : Fin N→Prop) (stage : Fin N→ℕ)
    (b : ∀t, Installed F groups ports lanes w m (key t).2 (atScale positive stage (key t).1 raw))
    (cap : {i : Fin N // ¬positive i} → ℕ)
    (words : (i:Fin N)→Fin (2^(raw i).width)) (history : Fin n → Bool) (index : Fin n) :
    nativePins (view:=view) key raw positive stage b cap words history
      (.inr (.inr (.inl index))) = history index := rfl

end Hierarchy.Tagged.WideCalendarSites
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
set_option maxHeartbeats 1600000
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

open LinearAlgebra.SpectralBooks.SiteTensor Tagged.PassiveWindow
local notation "K" => siteLast h d k+1
local notation "deg" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "bound" => v.wideNeighborCap width unit
local notation "ends" => sorted v.sampler perm.symm v.depth (shape).mark ∘ (shape).order
local notation "portsAt" => named v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order
local notation "socket" => shelfSlot («h»:=h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "here" => named_coordinate v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order
local notation "timer" => SignedSites.calendarTime (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unit)
local notation "boundAt" => v.wide_outer_lane h width unit
variable (ok : kept) (words : wordTable) (q : states) (j : Fin (es).length) (s : Fin K) (right : Bool)
local notation "timeAt" => if right then j.succ else j.castSucc
local notation "bits" => (shape).bits timeAt
local notation "fits" => fun r=>((shape).fits timeAt r false).trans (boundAt (portsAt (r,false)))
local notation "slotAt" => PacketNeighbor.localSlot ends bits portsAt socket here s
local notation "chart" => (shape).atWidth timeAt
local notation "parts" => carried ends bits s fits slotAt chart
local notation "current" => datedState tree ws s es top branch timeAt (q s)
local notation "assignment" => data ok words q
local notation "value" => Sum.elim e (Sum.elim record (Sum.elim assignment ((G).terminal out)))
local notation "tap" => LedgerStep.outerWord (cap:=bound) G es roles socket timer j s right

private theorem calendarAtPaidHistory {P₀ P₁ H P₃ J : Type}
    (numbering : (P₀ ⊕ (P₁ ⊕ (H ⊕ P₃))) ≃ J)
    (bank : (P₀ ⊕ (P₁ ⊕ (H ⊕ P₃))) → Bool) (date : H) (address : J)
    (location : address = EntryOrder.timePin numbering date)
    (timeline : H → Bool) (answer : Bool)
    (pinned : bank (.inr (.inr (.inl date))) = timeline date)
    (placed : timeline date = answer) :
    (bank ∘ numbering.symm) address = answer :=
  (congrArg (bank ∘ numbering.symm) location).trans
    ((congrArg bank (numbering.symm_apply_apply _)).trans (pinned.trans placed))

-- Read the native assignment retained by the paid day itself. Keeping that
-- exact term avoids rebuilding the selected report for every ranked-row field.
open Lean Meta in
private def readPaidCalendarOperands (lhs : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
    let some dayBody ← unfoldDefinition? lhs (ignoreTransparency := true)
      | throwError "could not open the selected purchased day"
    let mut body := dayBody
    for _ in [:24] do
      body := body.consumeMData
      let f := body.getAppFn
      if f.isLet then
        body := mkAppN (f.letBody!.instantiate1 f.letValue!) body.getAppArgs
      else if f.isLambda && body.isApp then body := body.headBeta
      else if body.isAppOf ``Function.comp || body.isAppOf ``nativePins then break
      else
        let some exposedDay ← unfoldDefinition? body (ignoreTransparency := true)
          | throwError "expected native day assignment, got {f}"
        body := exposedDay
    let (bank,undo) ← if body.isAppOfArity ``Function.comp 6 then
        pure (body.getAppArgs[3]!,body.getAppArgs[4]!)
      else if body.isAppOf ``nativePins && body.appArg!.isApp then
        pure (body.appFn!,body.appArg!.appFn!)
      else throwError "expected a numbered native day, got {body.getAppFn}"
    unless bank.isAppOf ``nativePins do throwError "expected the paid native row bank"
    let rec inverseOrder (remaining : Nat) (arg : Lean.Expr) : Option Lean.Expr :=
      match remaining with
      | 0 => none
      | remaining+1 =>
        if arg.isAppOfArity ``Equiv.symm 3 || arg.isAppOfArity ``Equiv.invFun 3 then some arg.getAppArgs.back!
        else match arg.consumeMData with
          | .app fn v => inverseOrder remaining v <|> inverseOrder remaining fn
          | .proj name index v => if name == ``Equiv && index == 1 then some v else inverseOrder remaining v
          | .lam _ _ bdy _ => inverseOrder remaining bdy
          | _ => none
    let some rowOrder := inverseOrder 10 undo
      | throwError "expected the inverse of the physical row numbering, got {undo.getAppFn}"
    return (bank,rowOrder)

open Lean Meta Elab Term in
local elab "numberingOfDay " observation:term : term => do
  let observed ← instantiateMVars (← elabTerm observation none)
  return (← readPaidCalendarOperands observed).2

-- Apply the transport rule to the original row and equality retained by its
-- numbering. The row metadata fixes every dependent argument of the rule.
open Lean Meta Elab Tactic in
local elab "transportPaidOrder " numbering:ident " with " test:term : tactic =>
  withMainContext do
    let main ← getMainGoal
    let rowOrder ← getFVarFromUserName numbering.getId
    let some originalOrder := (← rowOrder.fvarId!.getDecl).value? true
      | throwError "expected a locally named calendar numbering"
    let selected ← match originalOrder.consumeMData with
      | .proj _ _ r => pure r
      | tagged =>
        if tagged.isAppOf ``CalendarTerms.RankedRows.numbering then pure tagged.getAppArgs.back!
        else throwError "expected the numbering of a selected row, got {tagged.getAppFn}"
    let some ranked ← whnfUntil selected ``CalendarTerms.RankedRows.onBranch
      | throwError "expected the transported purchased row"
    let rule := mkAppN (mkConst ``CalendarTerms.RankedRows.onBranch_property ranked.getAppFn.constLevels!)
      ranked.getAppArgs
    let ruleType ← whnf (← inferType rule)
    unless ruleType.isForall do throwError "expected a ranked-row property"
    let predicate ← Lean.Elab.Term.elabTerm test (some ruleType.bindingDomain!)
    let ruleType ← whnf (ruleType.bindingBody!.instantiate1 predicate)
    unless ruleType.isForall do throwError "expected the original row property"
    let valid ← mkFreshExprSyntheticOpaqueMVar ruleType.bindingDomain!
    main.assign (mkApp2 rule predicate valid)
    replaceMainGoal [valid.mvarId!]

open Lean Meta Elab Tactic in
local elab "readPurchasedHistory " location:ident " using " numbering:ident " for " date:ident : tactic =>
  withMainContext do
    let main ← getMainGoal
    let wanted ← whnf (← instantiateMVars (← main.getType))
    unless wanted.isAppOfArity ``Eq 3 do throwError "expected a history-bit equation"
    let lhs := wanted.getAppArgs[1]!.consumeMData
    let rhs := wanted.getAppArgs[2]!.consumeMData
    let (bank,_) ← readPaidCalendarOperands lhs
    let rowOrder ← getFVarFromUserName numbering.getId
    let tableType ← whnf (← inferType rowOrder)
    unless tableType.isAppOfArity ``Equiv 2 do throwError "expected a row numbering"
    let split (t : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
      let v ← whnf t
      unless v.isAppOfArity ``Sum 2 do throwError "expected a sum of native pin banks"
      return (v.getAppArgs[0]!,v.getAppArgs[1]!)
    let (left,rest) ← split tableType.getAppArgs[0]!
    let (privateRows,rest) ← split rest
    let (timeline,outputRows) ← split rest
    let dateExpr ← getFVarFromUserName date.getId
    let atDate ← getFVarFromUserName location.getId
    let dayHistory := bank.getAppArgs.back!
    unless dayHistory.isAppOf ``placedBits do throwError "expected the paid party placement"
    let readDigit := mkAppN (mkConst ``paidNativeHistoryDigit bank.getAppFn.constLevels!)
      (bank.getAppArgs.push dateExpr)
    unless rhs.isApp && rhs.appFn!.isAppOf ``placedBits do
      throwError "expected the original party-bit placement"
    let physicalArgs := dayHistory.getAppArgs
    let expectedArgs := rhs.appFn!.getAppArgs
    let physicalPlace := physicalArgs[physicalArgs.size - 2]!
    let expectedPlace := expectedArgs[expectedArgs.size - 2]!
    let placementType ← inferType physicalPlace
    let atPlacement ← withLocalDeclD `bitPlacement placementType fun variation => do
      let newHistory := mkAppN dayHistory.getAppFn (physicalArgs.set! (physicalArgs.size - 2) variation)
      mkLambdaFVars #[variation] (mkApp newHistory dateExpr)
    let samePlacement ← mkEqRefl expectedPlace
    let originalDigit := mkAppN (mkConst ``congrArg [.succ .zero,.succ .zero])
      #[placementType,mkConst ``Bool,physicalPlace,expectedPlace,atPlacement,samePlacement]
    let proof := mkAppN (mkConst ``calendarAtPaidHistory)
      #[left,privateRows,timeline,outputRows,tableType.getAppArgs[1]!,rowOrder,bank,dateExpr,lhs.appArg!,atDate,dayHistory,rhs,readDigit,originalDigit]
    main.assign proof
    replaceMainGoal []

/-- The actual purchased and ranked row number decodes the canonical native
history argument at every date in the physical aperture. -/
theorem calendarDayPins_timed {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x)
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (ok : kept) (words : wordTable) (q : states)
    (n : Fin times) :
    assignment (timer n)=placedBits tree ws es top branch place q n := by
  let paidNumbering := numberingOfDay (assignment (timer n))
  let hist:=SignedSites.calendarHistory (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unit)
  have codes : EntryOrder.timePin paidNumbering=hist := by
    transportPaidOrder paidNumbering with (fun _ r=>EntryOrder.timePin r.numbering=hist)
    ext z
    rfl
  have addr : timer n=EntryOrder.timePin paidNumbering n :=
    (congrArg (fun f : Fin times ↪ D=>f n) codes).symm
  readPurchasedHistory addr using paidNumbering for n


/-- Every occupied source and target port of the actual selected dated
network reads the corresponding bit of its neighboring original state.
Row numbers, widths, role capacities and native output come from the same run. -/
theorem wide_calendar_day_outer_carried_bits {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x)
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (ok : kept) (words : wordTable) (q : states) (j : Fin (es).length) (s : Fin K) (right : Bool)
    :
    ∀column neighbor,(parts).owner column=some neighbor→∀digit:Fin ((parts).width column),
      Sum.elim value id (tap column (digit.castLE ((parts).within column)))=
        (current neighbor).val.testBit ((parts).base column+digit.val) := by
  have original := LedgerStep.outer_carried_read tree ws es top branch roles socket pins q timer j s right
    G e record assignment out ends bits portsAt ((shape).fits timeAt) fits here chart
    (v.wide_path_cells_numbered h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
      height.report height.wordRoom path unit height.replay height.measure
      (height.funded_aperture S unit Sfit v.calendarUnit_rate) timeAt) chart
    (v.calendarDayPins_timed m ell short u δ ξ x cpu support routeAge prices pricePos groupsFit metadata
      lanesFit buy e perm i tag height ok words q)
  exact original

/-- The same physical row remains readable after rebasing a dated chord width
to the native spill's carry-plus-active width at this site. -/
theorem wide_calendar_day_outer_rebased_bits {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x)
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (ok : kept) (words : wordTable) (q : states) (j : Fin (es).length) (s : Fin K) (right : Bool)
    {totalWidths : Widths K} (amount : installedWidths ends bits=totalWidths) :
    let r:=carried ends bits s fits slotAt amount
    let rebased:=cast (congrArg (fun U=>State U s) ((chart).symm.trans amount)) current
    ∀column neighbor,r.owner column=some neighbor→∀digit:Fin (r.width column),
      Sum.elim value id (tap column (digit.castLE (r.within column)))=(rebased neighbor).val.testBit (r.base column+digit.val) := by
  exact carried_cast_read ends bits s fits slotAt chart current (fun column digit=>Sum.elim value id (tap column digit))
    (v.wide_calendar_day_outer_carried_bits m ell short u δ ξ x cpu support routeAge prices pricePos
      groupsFit metadata lanesFit buy e perm i tag height ok words q j s right) ((chart).symm.trans amount)

/-- The signed input and the spill output use precisely the same real
carry rows even when the substeps are evaluated on an arbitrary middle word. -/
theorem wide_calendar_day_substep_carried_bits {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x)
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (ok : kept) (words : wordTable) (q : states) (j : Fin (es).length) (s : Fin K) (right : Bool)
    (mid : Fin (deg*bound)→Bool) :
    let ev:=Sum.elim e (Sum.elim record (Sum.elim (Sum.elim assignment mid) ((G).terminal out)))
    ∀column neighbor,(parts).owner column=some neighbor→∀digit:Fin ((parts).width column),
      Sum.elim ev id (LedgerStep.substepWord (cap:=bound) G es roles socket timer j s right right
        column (digit.castLE ((parts).within column)))=(current neighbor).val.testBit ((parts).base column+digit.val) := by
  intro ev col neighbor occ digit
  exact (LedgerStep.substepWord_outer G es roles socket timer j s e record assignment out mid right
    col (digit.castLE ((parts).within col))).trans
      (v.wide_calendar_day_outer_carried_bits m ell short u δ ξ x cpu support routeAge prices pricePos
        groupsFit metadata lanesFit buy e perm i tag height ok words q j s right col neighbor occ digit)

local notation "outBits" => (shape).bits j.succ
local notation "outFit" => fun r=>((shape).fits j.succ r false).trans (boundAt (portsAt (r,false)))
local notation "outSlot" => PacketNeighbor.localSlot ends outBits portsAt socket here s
local notation "outShape" => (shape).atWidth j.succ
local notation "outState" => datedState tree ws s es top branch j.succ (q s)

/-- The physical spill output retains the original chronological bits at
the rebased successor width, for every possible hidden intermediate word. -/
theorem calendar_day_spill_post_bits {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x)
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (ok : kept) (words : wordTable) (q : states) (j : Fin (es).length) (s : Fin K)
    (active : Widths K) (atWidth : installedWidths ends outBits=active)
    (mid : Fin (deg*bound)→Bool) :
    let r:=carried ends outBits s outFit outSlot atWidth
    let y:=cast (congrArg (fun axisWidths=>State axisWidths s) ((outShape).symm.trans atWidth)) outState
    let ev:=Sum.elim e (Sum.elim record (Sum.elim (Sum.elim assignment mid) ((G).terminal out)))
    ∀column neighbor,r.owner column=some neighbor→∀digit:Fin (r.width column),
      Sum.elim ev id (LedgerStep.substepWord (cap:=bound) G es roles socket timer j s true true
        column (digit.castLE (r.within column)))=(y neighbor).val.testBit (r.base column+digit.val) := by
  intro r y ev i₀ p owns digit
  exact (LedgerStep.substepWord_outer G es roles socket timer j s e record assignment out mid true i₀
    (digit.castLE (r.within i₀))).trans
      (v.wide_calendar_day_outer_rebased_bits m ell short u δ ξ x cpu support routeAge prices pricePos
        groupsFit metadata lanesFit buy e perm i tag height ok words q j s true atWidth i₀ p owns digit)


local notation "layout" => v.wideInstalledLayout x m ell short u δ ξ unit g
local notation "first" => (layout).pruneScratch+(layout).pruneRows+1
local notation "correct" => v.wideSpillDates h width ell unit v.maxBits first

/-- On a feed date neither input row is corrected. This uses the actual
printed branch flag, so the genuine old width and successor width are the
two physical spill scopes; the hypothetical correction column drops out. -/
theorem calendar_feed_carried_bits {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x)
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (ok : kept) (words : wordTable) (q : states) (j : Fin (es).length) (s : Fin K) (right : Bool)
    {event} (feed : (es).get j=.feed event)
    (correction : Fin (shape).count→ℕ) (rest : Widths K) (active : Bool→Widths K)
    (before : installedWidths ends (if (correct).attempt j then correction else (shape).bits j.castSucc)=rest+active false)
    (afterWidth : installedWidths ends ((shape).bits j.succ)=rest+active true) :
    let pre : installedWidths ends ((shape).bits j.castSucc)=rest+active false := by
      have no : (correct).attempt j=false:=by
        change (match (es).get j with | .attempt _=>true | .feed _=>false)=_
        rw [feed]
      simpa [no] using before
    let eqAt : installedWidths ends bits=rest+active right:=by cases right <;> first | exact pre | exact afterWidth
    let r:=carried ends bits s fits slotAt eqAt
    let y:=cast (congrArg (fun U=>State U s) ((chart).symm.trans eqAt)) current
    ∀column neighbor,r.owner column=some neighbor→∀digit:Fin (r.width column),
      Sum.elim value id (tap column (digit.castLE (r.within column)))=(y neighbor).val.testBit (r.base column+digit.val) := by
  intro pre eqAt
  exact v.wide_calendar_day_outer_rebased_bits m ell short u δ ξ x cpu support routeAge prices pricePos
    groupsFit metadata lanesFit buy e perm i tag height ok words q j s right eqAt

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
