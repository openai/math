import OAI.Hierarchy.TaggedWidePathRoleCells
import OAI.Hierarchy.TaggedWideOriginalDateFields

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
set_option maxHeartbeats 1600000
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
local notation "wire" => WireTelescope.CalendarTape.Prefix.atWidth (v.wideCursorWidth h width size π seed age budget small)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans expanse
local notation:max "cap" c:arg => HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh c v.keepLimit (CatalystArchive.fuel v.mesh) width
variable (unitCost:ℕ)
    (replay:v.cursorReplayHeight≤h) (measure:v.wideDatedLedgerHeight≤h)
    (bounded : ∀(perm:Equiv.Perm (Fin (2^h))) (mem:Boot.Tape h (2^v.W)),
      let o:=wideRouteOrder h (2^v.W) k
      let m:=v.wideSignedMidAt h width size stock v.radius perm o mem
      let c:=v.wideSignedCheckoutAt h width size stock v.radius perm o mem
      c ceiling=0→v.DatedWireFits h width perm m c unitCost)

local notation "evidence" => v.wide_reported_path_funded_rows h width size π seed age budget small expanse late room j
local notation "calibrated" => v.wide_funded_run_at h width v.radius π.symm raw v.maxBits size expanse
  (Classical.choose evidence) budget small (0:Word w)
local notation "reconciled" => (Classical.choose_spec calibrated).1
local notation "named" => v.widePathRoles h width size π seed age budget small expanse late room j unitCost replay measure bounded

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


local notation "positiveCount" => Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨.inl ⟨0,Nat.two_pow_pos _⟩⟩) v.positive

/-- The selected reconciliation fixes the dates of the original published fields. -/
abbrev widePathOriginalDateFields (ell unitCost work : ℕ) (image : Memory w) : Prop :=
  let pathEvidence := v.wide_reported_path_funded_rows h width size π seed age budget small expanse late room j
  let chosenHeight := Classical.choose pathEvidence
  let run := v.wide_funded_run_at h width v.radius π.symm raw v.maxBits size expanse chosenHeight budget small (0 : Word w)
  let receipt := Classical.choose_spec run
  let reconciliation := receipt.1
  let dates := selectedPathDates reconciliation
  v.originalDateFields h width size π.symm raw (dates := dates) (pos := positiveCount) reconciliation ell unitCost work image

/-- Transfer precisely the original three published fields at every boundary
of this reachable branch onto its actual chosen calendar-role numbering. -/
theorem wide_path_role_fields (ell work : ℕ) (earlier out : Memory w)
    (published : v.widePathOriginalDateFields h width size π seed age budget small expanse late room j ell unitCost work earlier)
    (survives : ∀i,i<(v.wideDated h width ell unitCost).rolesEnd work → out i=earlier i) :
    ∀t : Fin ((es).length+1),∀f : Fin 3,DatedRoleSheets.roleFact
      (v.wideDated h width ell unitCost).physical v.sampler π.symm v.depth (named).mark (named).exclusive
      (named).order ((v.wideDated h width ell unitCost).roleStart work t) ((named).bits t) (named).ident out f :=
  by
    let pathEvidence := v.wide_reported_path_funded_rows h width size π seed age budget small expanse late room j
    let chosenHeight := Classical.choose pathEvidence
    let run := v.wide_funded_run_at h width v.radius π.symm raw v.maxBits size expanse chosenHeight budget small (0 : Word w)
    let receipt := Classical.choose_spec run
    let reconciliation := receipt.1
    let dates := selectedPathDates reconciliation
    have fields := originalDateFields.after v h width size π.symm raw (dates := dates) (pos := positiveCount)
      reconciliation ell unitCost work published survives
    exact fields

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
