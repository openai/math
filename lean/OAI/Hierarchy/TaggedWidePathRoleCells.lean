import OAI.Hierarchy.TaggedWideNumberedBranchRoles
import OAI.Hierarchy.TaggedWideFundedBoundary
import OAI.Hierarchy.TaggedWideFundedCursorRows
import OAI.Hierarchy.TaggedWireFundedContinuation

namespace OAI
/-! # The original site-bit placements of a complete signed categorical path -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets WireTelescope Tagged CalendarTape
open CoreBoard.PhysicalTerm Filter
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 4500000
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
local notation "cap" c => HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
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


/-- All placements use the original order of the signed output. An intermediate
cursor is identified with the authentic native tape by the causal replay theorem. -/
def widePathRoles : BranchRoles v.sampler π.symm v.depth (cap unitCost) wire j :=
  let evidence:=v.wide_reported_path_funded_rows h width size π seed age budget small expanse late room j
  let a:=Classical.choose evidence
  let bill:=Classical.choose evidence.choose_spec
  let alignment {entries : ℕ} (site : Fin entries → Fin (Fintype.card (Columns h (2^v.W))*k)) (fees : Fin entries → ℕ) :=
    (Classical.choose evidence.choose_spec.choose_spec) site fees
  let accepted:=evidence.choose_spec.choose_spec.choose_spec.1
  let run:=v.wide_funded_run_at h width v.radius π.symm raw v.maxBits size expanse a budget small (0:Word w)
  let recpt:=Classical.choose_spec run
  let reconciliation := recpt.1
  let selectedDates := selectedPathDates reconciliation
  let result := v.numberedBranchRoles h width size π.symm raw expanse a budget small bill unitCost j wire
    (dates := selectedDates) (pos := Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨.inl ⟨0,Nat.two_pow_pos _⟩⟩) v.positive)
    reconciliation (alignment _ _) (bounded π.symm tape accepted) (fun t => by
      let paidAt := v.wide_dated_wire h width size π.symm raw expanse measure small budget (0:Word w) t.val
        (Nat.lt_succ_iff.mp t.isLt)
      let pathAt := v.wide_funded_boundary h width size π seed age budget small arenaRoom replay j t
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          let first ← Lean.Meta.getFVarFromUserName `pathAt
          let second ← Lean.Meta.getFVarFromUserName `paidAt
          let required ← Lean.Meta.whnf (← goal.getType)
          let firstType ← Lean.Meta.whnf (← Lean.Meta.inferType first)
          let #[carrier, leftEnd, rightEnd] := required.getAppArgs | throwError "expected an equality of installed widths"
          let #[_, _, common] := firstType.getAppArgs | throwError "expected the path boundary equality"
          let univs := required.getAppFn.constLevels!
          let composed := Lean.mkAppN (Lean.mkConst ``Eq.trans univs) #[carrier, rightEnd, common, leftEnd, first, second]
          goal.assign (Lean.mkAppN (Lean.mkConst ``Eq.symm univs) #[carrier, rightEnd, leftEnd, composed])
        Lean.Elab.Tactic.replaceMainGoal [])
  result

local notation "rows" => fun (l : WireTelescope.CalendarTape.Path slots es start) =>v.widePathRoles h width size π seed age budget small expanse late room l
  unitCost replay measure bounded
local notation "total" => fun (c : WireTelescope.CalendarTape.Prefix.Cursor slots es start) =>v.wide_funded_continuation h width size arenaRoom π seed age budget small c.path

def widePathCells := BranchRoles.cells total rows j

theorem wide_path_cells_numbered (t:Fin ((es).length+1)) :
    v.widePathCells h width size π seed age budget small expanse late room j unitCost replay measure bounded
      (WireTelescope.CalendarTape.Prefix.boundaryIndex j t)=BranchRoles.atTime rows j t :=
  BranchRoles.cells_at total rows j t

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
