import OAI.Hierarchy.TaggedWireReportedPath
import OAI.Hierarchy.TaggedWideCursorReportRows

namespace OAI
/-! # Complete report and geometry from the original signed terminal state -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
set_option maxRecDepth 8192
set_option maxHeartbeats 320000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width

local notation "D" => 2^v.W

local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies

open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram

local notation "rows" => (P).catalogue.rows

local notation "stock" => v.fixedTerminalStock P h width

local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length

local notation "o" => wideRouteOrder h D k

variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock v.radius π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π o seed

local notation "pair" => pairKeys (Columns h D) k
private abbrev packedStateCost :=
  ∀e : Fin rows, PaidWidths.total ss chk e + (v.overflowFactor v.keepLimit + fuel v.mesh) * width < 2^w

variable (horizon : v.wideFundedSize h width bits ≤ size) (age : v.wideFundedHeight ≤ h)
    (budget : v.keepLimit * width + 1 ≤ 2^h) (small : width ≤ 2^h)
    (cost : packedStateCost v h width size π raw bits)
open LinearAlgebra.SpectralBooks ChordGraph
local notation "es" => events v.mesh
local notation "endRam" => run C es mid
local notation "stored" => (P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) chk
local notation "live" => (P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) endRam
local notation "charges" => v.wirePaidAt h width bits last endRam
private abbrev packedStateNames := ∀{n : ℕ}(owner : Fin n→Fin num)(fees : Fin n→ℕ),
    v.WideFundedAlignment h width size bits π raw owner fees (fun j=>(pair j).val)
variable (state : Word (Native.wordBits h (2^v.W) Native.copies)) (names : packedStateNames v h width size π raw bits)
local notation "Z" => v.wide_native_report h width size π raw bits horizon age budget small cost state names

/- Refer to the original issued report using the finite width recorded by its
terminal projection. Its defining value is the native report application. -/
open Lean Elab Term in
local elab "compactPathNative " candidate:term : term => do
  let entry ← elabTerm candidate none
  unless entry.getAppFn.isConstOf ``wide_native_report do
    throwError "expected the original issued report"
  let result ← getConstInfo ``native_state_report_rows
  let some sourceCall :=  result.type.find? (fun e =>
    e.isApp && e.getAppFn.constName?.any (fun c => c.getString! == "terminalInputReport"))
    | throwError "the signed row projection contains no original report"
  let compact := mkAppN sourceCall.getAppFn entry.getAppArgs
  let typ ← Meta.whnf (← Meta.inferType compact)
  unless typ.getAppFn.isConstOf ``CoreBoard.Report do throwError "expected a fixed-board report"
  return compact

/-- The original signed native report at the width index certified by its issued row table. -/
abbrev signedPathNativeReport :=
  compactPathNative (v.wide_native_report h width size π raw bits horizon age budget small cost state names)

/-- The report paired with the width ledger that it realizes. -/
private def packedStateReport
    {height depth indexWidth inputWidth allowance radius denominator : ℕ}
    {permutation : Equiv.Perm (Tagged.Row height)} {initial : Widths (siteLast height depth indexWidth+1)}
    (entry : CoreBoard.Report permutation depth indexWidth inputWidth allowance radius denominator initial) :
    (widths : Widths (siteLast height depth indexWidth+1)) ×
      CoreBoard.Report permutation depth indexWidth inputWidth allowance radius denominator widths :=
  ⟨initial, entry⟩

private theorem packed_replacement {height depth indexWidth inputWidth allowance radius denominator : ℕ}
    {permutation : Equiv.Perm (Tagged.Row height)} {initial final : Widths (siteLast height depth indexWidth+1)}
    (entry : CoreBoard.Report permutation depth indexWidth inputWidth allowance radius denominator initial)
    (credit : entry.mount.actual.chordWidths entry.fixed +
      (commodityGraph permutation.symm (siteNumber height depth indexWidth)).chordWidths entry.stock +
      (catalystGraph (siteNumber height depth indexWidth)).chordWidths (fun i => entry.reserved i-entry.used i) = final) :
    packedStateReport ({entry with ledger := credit} :
      CoreBoard.Report permutation depth indexWidth inputWidth allowance radius denominator final) = packedStateReport entry := by
  have same : initial = final := entry.ledger.symm.trans credit
  cases same
  rfl

attribute [local irreducible] PortGraph.chordWidths commodityGraph catalystGraph siteNumber
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit
  wide_report_for_dates wide_native_report wide_report_at wireAt wideFundedSize wideSignedMidAt wideSignedCheckoutAt

/- Recover the kernel's finite-width alias for the original native report from
its already-checked projection. This extracts a term, not a proof assumption. -/
open Lean Elab Term in
local elab "sourceOfNativeRows " arg:term : term => do
  let evidence ← elabTerm arg none
  let typ ← Meta.whnf (← Meta.inferType evidence)
  unless typ.getAppFn.isConstOf ``Eq do throwError "expected an original native report projection equality"
  let rhs := typ.getAppArgs[2]!
  let native := rhs.getAppArgs.back!
  let natural ← Meta.whnf (← Meta.inferType native)
  unless natural.getAppFn.isConstOf ``CoreBoard.Report do throwError "expected original native report"
  return native

open Lean Elab Term in
local elab "packedReportPair " x:term " comparedWith " y:term : term => do
  let left ← elabTerm x none
  let right ← elabTerm y none
  let packed (r : Lean.Expr) : TermElabM Lean.Expr := do
    let typ ← Meta.whnf (← Meta.inferType r)
    unless typ.getAppFn.isConstOf ``CoreBoard.Report do throwError "expected CoreBoard.Report"
    let a := typ.getAppArgs
    return mkAppN (mkConst ``packedStateReport typ.getAppFn.constLevels!)
      #[a[0]!, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!, a[1]!, a[8]!, r]
  let l ← packed left
  let r ← packed right
  let space ← Meta.inferType l
  let sort ← Meta.getLevel space
  return mkApp3 (mkConst ``Eq [sort]) space l r

private theorem native_state_report_packed
    (stable : ∀e,(charges) e=v.wirePaidAt h width bits last chk e)
    (ends : ∀e,0<(charges) e→(live).actual.tail e=(stored).actual.tail e ∧
      (live).actual.head e=(stored).actual.head e) :
    packedReportPair (v.native_state_report h width size π raw bits horizon age budget small cost state names stable ends) comparedWith (sourceOfNativeRows (v.native_state_report_rows h width size π raw bits horizon age budget small cost state names stable ends)) := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let target ← Lean.instantiateMVars (← goal.getType)
      let args := target.getAppArgs[1]!.getAppArgs
      let value := args.back!
      unless value.getAppFn.isConstOf ``native_state_report do
        throwError "expected the terminal native report"
      let some projectedBody ← Lean.Meta.unfoldDefinition? value true
        | throwError "could not open the native report projection"
      let actual (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let mut v := e.headBeta
        while v.isFVar do
          let decl ← v.fvarId!.getDecl
          let some val := decl.value? true | break
          v := val.headBeta
        return v
      let result ← Lean.Meta.lambdaLetTelescope projectedBody fun projectedLets proj => do
        let projected ← actual proj
        let .proj _ 0 retained := projected | throwError "expected a stored report; found {projected.getAppFn}"
        let choice ← actual retained
        let some chosenBody ← Lean.Meta.unfoldDefinition? choice true | throwError "missing selected report"
        let solved ← Lean.Meta.lambdaLetTelescope chosenBody fun chosenLets body => do
          let replacement ← actual body
          let some fn := replacement.getAppFn.constName? | throwError "expected the ledger replacement call"
          unless fn.getString! == "replaceVectorLedger" do throwError "unexpected report constructor {fn}"
          let exactReplacement := Lean.mkAppN (Lean.mkConst ``packed_replacement replacement.getAppFn.constLevels!) replacement.getAppArgs
          Lean.Meta.mkLetFVars chosenLets exactReplacement (generalizeNondepLet := false)
        Lean.Meta.mkLetFVars projectedLets solved (generalizeNondepLet := false)
      goal.assign result
      Lean.Elab.Tactic.replaceMainGoal []

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets WireTelescope Tagged CalendarTape
open CoreBoard.PhysicalTerm Filter
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false

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
variable (j : CalendarTape.Path (v.wideSelector h width age budget small).format.slot
    (events v.mesh) (v.wideOrigin h width size seed π))
local notation "raw" => (reader).format.windows.header es (encode slots es start j) seed
local notation "tape" => v.wideFundedRaw h width v.maxBits raw
local notation "checkout" => v.wideSignedCheckoutAt h width size stock v.radius π.symm
  (wideRouteOrder h (2^v.W) k) tape
local notation "pathReport" => v.wide_reported_path h width size π seed age budget small expanse late room j


local notation "alignmentWords" => Fintype.card (Columns h (2^v.W)) * k
local notation "paidCost" => ∀ e : Fin (table).catalogue.rows,
  PaidWidths.total (v.widePaidSlices h width v.maxBits) checkout e +
    (v.overflowFactor v.keepLimit + fuel v.mesh) * width < 2^w
local notation "nameAlignment" => ∀ {n : ℕ} (owner : Fin n → Fin alignmentWords) (fees : Fin n → ℕ),
  v.WideFundedAlignment h width size v.maxBits π.symm raw owner fees
    (fun z => (CatalystArchive.pairKeys (Columns h (2^v.W)) k z).val)
local notation "ReportSpace" => (U : _) × CoreBoard.Report π (2^v.W) k width (fuel v.mesh*width) v.radius 1 U
local notation "pathValue" => (⟨_,pathReport⟩ : ReportSpace)
local notation "native" a:arg c:arg ns:arg => v.signedPathNativeReport h width size π.symm raw v.maxBits expanse a budget small c (0 : Word w) ns
local notation "nrows" => (v.widePlacement h width).catalogue.rows
local notation "RowSpace" => (lines : Fin nrows → ProtocolRAMEmit.Row) ×
  ProtocolRAMEmit.Geometry (boardLayout h (2^v.W) k width (fuel v.mesh*width)) v.radius 1 lines
local notation "tableOf" r:arg => (⟨(r).rows,(r).geometry⟩ : RowSpace)


private theorem pack_transportLedger {n d k wt R M den : ℕ} {perm : Equiv.Perm (Tagged.Row n)}
    {U V} (r : CoreBoard.Report perm d k wt R M den U) (e : U=V) :
    (⟨V,Report.transportLedger r e⟩ : (index : _) × CoreBoard.Report perm d k wt R M den index)
       = ⟨U,r⟩ := by
  cases e
  cases r
  rfl


/-- All fields of the original signed terminal report survive the two changes
of ledger proof, including the mount, enumeration, receipt and paid widths. -/
theorem wide_reported_path_signed_packed :
    ∃ (admitted : v.wideFundedHeight≤h) (cost : paidCost) (names : nameAlignment),checkout ceiling=0 ∧
      pathValue=⟨_,(native admitted cost names)⟩ := by
  have preAge := (le_max_left _ _).trans late
  have admitted : v.wideFundedHeight ≤ h := (le_max_left ..).trans preAge
  have nameAge : Classical.choose (eventually_atTop.1 v.wide_funded_alignment) ≤ h :=
    (le_max_right ..).trans preAge
  have bound := (v.wide_funded_extent h width v.maxBits).trans expanse
  have accept := v.wide_funded_path h width age budget small v.maxBits size bound v.radius π.symm seed j
  have cost : paidCost := room size bound π.symm tape accept
  let names : nameAlignment := fun site fees =>
    Classical.choose_spec (eventually_atTop.1 v.wide_funded_alignment) h nameAge
      width v.maxBits size expanse small budget π.symm raw site fees
      (fun z => (CatalystArchive.pairKeys (Columns h (2^v.W)) k z).val)
  refine ⟨admitted,cost,names,accept,?_⟩
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let equality ← Lean.instantiateMVars (← goal.getType)
      let packed := equality.getAppArgs[1]!
      unless packed.getAppFn.isConstOf ``Sigma.mk do throwError "expected a width-indexed path report"
      let path := packed.getAppArgs.back!
      let some body ← Lean.Meta.unfoldDefinition? path true | throwError "no path report definition"
      let actual (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let mut value := e.headBeta
        while value.isFVar do
          let decl ← value.fvarId!.getDecl
          let some val := decl.value? true | break
          value := val.headBeta
        return value
      let packedNative (value : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let update ← actual value
        unless update.getAppFn.isConstOf ``Report.transportLedger do
          throwError "expected a report ledger update, got {update.getAppFn}"
        let nativeValue ← actual update.getAppArgs[update.getAppNumArgs-2]!
        unless nativeValue.getAppFn.isConstOf ``native_state_report do
          throwError "expected an authenticated state report, got {nativeValue.getAppFn}"
        let preserved := Lean.mkAppN (Lean.mkConst ``pack_transportLedger update.getAppFn.constLevels!) update.getAppArgs
        let original := Lean.mkAppN (Lean.mkConst ``native_state_report_packed nativeValue.getAppFn.constLevels!) nativeValue.getAppArgs
        let ty ← Lean.Meta.whnf (← Lean.Meta.inferType preserved)
        let aa := ty.getAppArgs
        let bb := (← Lean.Meta.whnf (← Lean.Meta.inferType original)).getAppArgs
        return Lean.mkAppN (Lean.mkConst ``Eq.trans ty.getAppFn.constLevels!) #[aa[0]!, aa[1]!, aa[2]!, bb[2]!, preserved, original]
      let result ← Lean.Meta.lambdaLetTelescope body fun vars term => do
        let terminal ← actual term
        let proof ← packedNative terminal
        Lean.Meta.mkLetFVars vars proof (generalizeNondepLet := false)
      goal.assign result
      Lean.Elab.Tactic.replaceMainGoal []


/-- The numbered rows and their geometry come from the same signed terminal report. -/
theorem wide_reported_path_signed_geometry :
    ∃ (admitted : v.wideFundedHeight≤h) (cost : paidCost) (names : nameAlignment), checkout ceiling=0 ∧
      reportGeometry π pathReport = reportGeometry π (native admitted cost names) := by
  obtain ⟨admitted,cost,names,accepted,whole⟩ :=
    v.wide_reported_path_signed_packed h width size π seed age budget small expanse late room j
  exact ⟨admitted,cost,names,accepted,congrArg (fun a : ReportSpace => reportGeometry π a.2) whole⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
