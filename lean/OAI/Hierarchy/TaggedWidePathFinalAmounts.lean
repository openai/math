import OAI.Hierarchy.TaggedWideNumberedFinalAmounts
import OAI.Hierarchy.TaggedWidePathRoleCells

namespace OAI
/-! # Final socket quantities on the authenticated funded path -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets WireTelescope Tagged CalendarTape
open CoreBoard.PhysicalTerm Filter
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

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

attribute [local irreducible] Nat.pow numberedBranchRoles
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit

/-- Selection of the terminal report uses the same dated signed run as the
physical branch rows, including its named commodity and reserve stock. -/
theorem wide_path_final_amounts :
    let evidence:=v.wide_reported_path_funded_rows h width size π seed age budget small expanse late room j
    let admitted:=Classical.choose evidence
    let bill:=Classical.choose evidence.choose_spec
    let alignment {entries : ℕ} (site : Fin entries → Fin (Fintype.card (Columns h (2^v.W)) * k)) (fees : Fin entries → ℕ) :=
      (Classical.choose evidence.choose_spec.choose_spec) site fees
    let Z:=compactPathNative (v.wide_native_report h width size π.symm raw v.maxBits expanse admitted budget small
      bill (0:Word w) (@alignment))
    let q:=v.widePathRoles h width size π seed age budget small expanse late room j
      unitCost replay measure bounded
    q.bits (Fin.last (es).length)=SettledMatrix.Layout.available Z.fixed Z.stock Z.reserved Z.used ∘
      HistoryRoles.DatedRows.embed v.sampler π.symm v.depth q.mark (table).catalogue (v.wideOrder h width)
        (v.wide_dated_bought_rows h width) ∘ q.order := by
  intro evidence admitted bill alignment selectedReport roleRows
  run_tac Lean.Elab.Tactic.withMainContext do
    let roles ← Lean.Meta.getLocalDeclFromUserName `roleRows
    let report ← Lean.Meta.getLocalDeclFromUserName `selectedReport
    let some roleExpr := roles.value? | throwError "expected the selected branch roles"
    let some reportExpr := report.value? | throwError "expected the selected funded report"
    let rolesCall ← Lean.Meta.whnf roleExpr
    let reportCall := reportExpr.headBeta
    unless rolesCall.getAppFn.isConstOf ``numberedBranchRoles && (reportCall.getAppFn.isConstOf ``wide_native_report || reportCall.getAppFn.constName?.any (fun n => n.getString! == "terminalInputReport")) do
      throwError "expected the chosen numbered roles and their native report"
    let roleArgs := rolesCall.getAppArgs
    let reportArgs := reportCall.getAppArgs
    let stateAndAlignment := reportArgs.extract (reportArgs.size-2) reportArgs.size
    let receiptIndex := roleArgs.size-4
    let theoremFn ← Lean.Meta.mkConstWithFreshMVarLevels ``numbered_final_amounts
    let proof := Lean.mkAppN theoremFn (roleArgs.extract 0 receiptIndex ++ stateAndAlignment ++ roleArgs.extract receiptIndex roleArgs.size)
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
